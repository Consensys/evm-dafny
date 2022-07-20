/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
package dafnyevm;

import static EVM_Compile.__default.create;
import static EVM_Compile.__default.execute;

import java.math.BigInteger;
import java.util.Map;

import EVM_Compile.State;
import EVM_Compile.State_INVALID;
import EVM_Compile.State_OK;
import EVM_Compile.State_RETURNS;
import EVM_Compile.State_REVERT;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafnyevm.util.Hex;


/**
 * An API which wraps the Dafny-generated classes to interacting with the Dafny
 * EVM simpler.
 *
 * @author David J. Pearce
 *
 */
public class DafnyEvm {
	/**
	 * Tracer is used for monitoring EVM state during execution.
	 */
	private Tracer tracer = DEFAULT_TRACER;
	/**
	 * Initial state of storage prior.
	 */
	private final DafnyMap<BigInteger,BigInteger> storage;
	/**
	 * EVM Bytecode to execute
	 */
	private final DafnySequence<Byte> code;

	/**
	 * Construct a Dafny Evm with a given initial storage and bytecode sequence.
	 *
	 * @param storage
	 * @param code
	 */
	public DafnyEvm(Map<BigInteger,BigInteger> storage, byte[] code) {
		this.storage = new DafnyMap<>(storage);
		this.code = DafnySequence.fromBytes(code);
	}

	/**
	 * Set the tracer to use during execution of this EVM.
	 *
	 * @param tracer
	 * @return
	 */
	public DafnyEvm setTracer(Tracer tracer) {
		this.tracer = tracer;
		return this;
	}

	/**
	 * Execute an external call using this EVM from a given externally owned
	 * account.
	 *
	 * @param from     The externally owned account.
	 * @param calldata Input supplied with the call.
	 * @return
	 */
	public SnapShot call(BigInteger from, byte[] calldata) {
		// Create call context.
		Context_Compile.Raw ctx = Context_Compile.__default.create(from, DafnySequence.fromBytes(calldata));
		// Create the EVM
		EVM_Compile.T evm = create(ctx, storage, BigInteger.ONE, code);
		// Execute it!
		State r = execute(new State_OK(evm));
		// Continue whilst the EVM is happy.
		while(r instanceof State_OK) {
			tracer.step(((State_OK)r).evm);
			r = execute(r);
		}
		// Final step
		tracer.step(evm);
		// Decide what happened
		if(r instanceof State_RETURNS) {
			State_RETURNS rret = (State_RETURNS) r;
			tracer.end(rret.data,BigInteger.ZERO);
			return new SnapShot(false,rret.data,rret.gas,evm);
		} else if(r instanceof State_REVERT) {
			State_REVERT rrev = (State_REVERT) r;
			tracer.revert(rrev.data,BigInteger.ZERO);
			return new SnapShot(true,rrev.data,rrev.gas,evm);
		} else {
			// Sanity check is invalid
			State_INVALID rinv = (State_INVALID) r;
			tracer.exception(BigInteger.ZERO);
			return new SnapShot(false,null,null,evm);
		}
	}

	/**
	 * A simple class capturing the output of an execution, including the full
	 * machine state.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class SnapShot {
		/**
		 * Indicates if a revert occurred.
		 */
		private final boolean revert;
		/**
		 * Return data (which is null if none).
		 */
		private final DafnySequence<? extends Byte> data;
		/**
		 * Gas returned (null if none).
		 */
		private final BigInteger gas;
		/**
		 * State of the EVM (so we can query it).
		 */
		private final EVM_Compile.T state;

		public SnapShot(EVM_Compile.T state) {
			this(false,null,null,state);
		}

		public SnapShot(boolean revert, DafnySequence<? extends Byte> data, BigInteger gas, EVM_Compile.T state) {
			this.revert = revert;
			this.data = data;
			this.gas = gas;
			this.state = state;
		}

		/**
		 * Determine whether execution reverted (or not).
		 *
		 * @return
		 */
		public boolean isRevert() {
			return revert;
		}

		/**
		 * Indicates exceptional outcome.
		 *
		 * @return
		 */
		public boolean isInvalid() {
			return data == null;
		}

		/**
		 * Get current <code>pc</code> value.
		 */
		public BigInteger getPC() {
			return state.pc;
		}

		/**
		 * Get current opcode.
		 *
		 * @return
		 */
		public int getOpcode() {
			return state.code.contents.select(state.pc).intValue() & 0xff;
		}

		/**
		 * Get remaining gas.
		 *
		 * @return
		 */
		public BigInteger getRemainingGas() {
			return state.gas;
		}

		/**
		 * Get any return data from this contract call. <code>null</code> indicates
		 * something went wrong.
		 *
		 * @return
		 */
		public DafnySequence<? extends Byte> getReturnData() {
			return data;
		}

		/**
		 * Get the state of the storage when the machine halted.
		 *
		 * @return
		 */
		public DafnyMap<? extends BigInteger,? extends BigInteger> getStorage() {
			return state.storage.contents;
		}

		/**
		 * Get the state of memory at this point in time.
		 *
		 * @return
		 */
		public byte[] getMemory() {
			// FIXME: this is something of a hack for now due to the way in which I have
			// implemented memory (i.e. as a map). This should be corrected at some point to
			// be a sequence.
			byte[] bytes = new byte[getMemorySize()];
			//
			DafnySet<? extends BigInteger> keys =state.memory.contents.keySet();
			// Determine largest address in use!
			for (BigInteger key : keys.Elements()) {
				int address = key.intValueExact();
				bytes[address] = state.memory.contents.get(key);
			}
			// Done
			return bytes;
		}

		public int getMemorySize() {
			DafnySet<? extends BigInteger> keys =state.memory.contents.keySet();
			BigInteger max = BigInteger.ZERO;
			// Determine largest address in use!
			for (BigInteger addr : keys.Elements()) {
				addr = addr.add(BigInteger.ONE);
				if (max.compareTo(addr) < 0) {
					max = addr;
				}
			}
			return max.intValueExact();
		}


		/**
		 * Get the state of the stack when the machine halted.
		 *
		 * @return
		 */
		public DafnySequence<? extends BigInteger> getStack() {
			return state.stack.contents;
		}

		@Override
		public String toString() {
			final String p = state.pc.toString();
			final String m = state.memory.contents.toString();
			final String s = state.storage.contents.toString();
			final String a = state.stack.contents.toString();
			return String.format("pc=%s, storage=%s, memory=%s, stack=%s", p, s, m, a);
		}
	}


	/**
	 * A tracer is used to extract internal state during execution of the EVM.
	 * @author David J. Pearce
	 *
	 */
	public interface Tracer {
		/**
		 * Identifies that the EVM has taken a single step of execution (i.e. executed a
		 * bytecode).
		 *
		 * @param evm
		 */
		public void step(EVM_Compile.T evm);

		/**
		 * Identifies that execution of the outermost contract call has ended with
		 * either a STOP or RETURN.
		 *
		 * @param output  --- Any return data provided.
		 * @param gasUsed --- The amount of gas used for the call.
		 */
		public void end(DafnySequence<? extends Byte> output, BigInteger gasUsed);

		/**
		 * Identifies that execution of the outermost contract call has ended with a
		 * REVERT.
		 *
		 * @param output  --- Any return data provided.
		 * @param gasUsed --- The amount of gas used for the call.
		 */
		public void revert(DafnySequence<? extends Byte> output, BigInteger gasUsed);

		/**
		 * Identifies that execution of the outermost contract call has ended with an
		 * exception.
		 *
		 * @param gasUsed --- The amount of gas used for the call.
		 */
		public void exception(BigInteger gasUsed);
	}

	/**
	 * The default tracer does nothing at all.
	 */
	public static final Tracer DEFAULT_TRACER = new Tracer() {

		@Override
		public void step(EVM_Compile.T evm) {}

		@Override
		public void end(DafnySequence<? extends Byte> output, BigInteger gasUsed) {
			byte[] bytes = output.toByteArray((DafnySequence<Byte>) output);
			System.out.println(Hex.toHexString(bytes));
		}

		@Override
		public void revert(DafnySequence<? extends Byte> output, BigInteger gasUsed) {
			byte[] bytes = output.toByteArray((DafnySequence<Byte>) output);
			System.out.println(Hex.toHexString(bytes));
			System.out.println("error: execution reverted");
		}

		@Override
		public void exception(BigInteger gasUsed) {
			// TODO: add error information
			System.out.println("error");
		}
	};

	/**
	 * The trace adaptor provides a more convenient API over the internal tracer
	 * API. The reason for this class existing is just to improve performance when
	 * the default tracer is being used.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static abstract class TraceAdaptor implements Tracer {
		@Override
		public final void step(EVM_Compile.T evm) {
			this.step(new SnapShot(evm));
		}

		@Override
		public final void end(DafnySequence<? extends Byte> output, BigInteger gasUsed) {
			end(output.toByteArray((DafnySequence<Byte>) output),gasUsed);
		}

		@Override
		public void revert(DafnySequence<? extends Byte> output, BigInteger gasUsed) {
			revert(output.toByteArray((DafnySequence<Byte>) output),gasUsed);
		}

		public abstract void step(SnapShot state);

		public abstract void end(byte[] output, BigInteger gasUsed);

		public abstract void revert(byte[] output, BigInteger gasUsed);
	}

}
