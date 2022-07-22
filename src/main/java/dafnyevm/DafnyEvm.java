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
import EVM_Compile.State_REVERTS;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafnyevm.util.Hex;
import dafnyevm.util.Tracers;

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
	private Tracer tracer = new Tracers.Default();
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
		State r = create(ctx, storage, BigInteger.ONE, code);
		// Execute it!
		tracer.step(r);
		r = execute(r);
		// Continue whilst the EVM is happy.
		while(r instanceof State_OK) {
			tracer.step(r);
			r = execute(r);
		}
		// Final step
		tracer.step(r);
		// Done
		return new SnapShot(r);
	}

	/**
	 * A snapshot of the current EVM state. This is effectively a wrapper around the
	 * <code>EVM.State</code> structure which exists on the Dafny side.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class SnapShot {
		/**
		 * State of the EVM (so we can query it).
		 */
		private final State state;

		public SnapShot(State state) {
			this.state = state;
		}

		/**
		 * Determine whether execution reverted (or not).
		 *
		 * @return
		 */
		public boolean isRevert() {
			return state instanceof State_REVERTS;
		}

		/**
		 * Indicates exceptional outcome.
		 *
		 * @return
		 */
		public boolean isInvalid() {
			return state instanceof State_INVALID;
		}

		/**
		 * Get current <code>pc</code> value.
		 */
		public BigInteger getPC() {
			State_OK sok = (State_OK) state;
			return sok.evm.pc;
		}

		/**
		 * Get current opcode.
		 *
		 * @return
		 */
		public int getOpcode() {
			State_OK sok = (State_OK) state;
			return sok.evm.code.contents.select(sok.evm.pc).intValue() & 0xff;
		}

		/**
		 * Get remaining gas.
		 *
		 * @return
		 */
		public BigInteger getRemainingGas() {
			State_OK sok = (State_OK) state;
			return sok.evm.gas;
		}

		/**
		 * Get any return data from this contract call. <code>null</code> indicates
		 * something went wrong.
		 *
		 * @return
		 */
		public DafnySequence<? extends Byte> getReturnData() {
			if(state instanceof State_RETURNS) {
				State_RETURNS sr = (State_RETURNS) state;
				return sr.data;
			} else if(state instanceof State_REVERTS) {
				State_REVERTS sr = (State_REVERTS) state;
				return sr.data;
			} else{
				return null;
			}
		}

		/**
		 * Get the state of the storage when the machine halted.
		 *
		 * @return
		 */
		public DafnyMap<? extends BigInteger,? extends BigInteger> getStorage() {
			State_OK sok = (State_OK) state;
			return sok.evm.storage.contents;
		}

		/**
		 * Get the state of memory at this point in time.
		 *
		 * @return
		 */
		public byte[] getMemory() {
			State_OK sok = (State_OK) state;
			DafnyMap<? extends BigInteger, ? extends Byte> memory = sok.evm.memory.contents;
			// FIXME: this is something of a hack for now due to the way in which I have
			// implemented memory (i.e. as a map). This should be corrected at some point to
			// be a sequence.
			byte[] bytes = new byte[getMemorySize()];
			//
			DafnySet<? extends BigInteger> keys = memory.keySet();
			// Determine largest address in use!
			for (BigInteger key : keys.Elements()) {
				int address = key.intValueExact();
				bytes[address] = memory.get(key);
			}
			// Done
			return bytes;
		}

		public int getMemorySize() {
			State_OK sok = (State_OK) state;
			DafnyMap<? extends BigInteger, ? extends Byte> memory = sok.evm.memory.contents;
			DafnySet<? extends BigInteger> keys = memory.keySet();
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
			State_OK sok = (State_OK) state;
			return sok.evm.stack.contents;
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
		public void step(State st);
	}

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
		public final void step(State st) {
			if(st instanceof State_OK) {
				step(new SnapShot(st));
			} else if(st instanceof State_RETURNS) {
				State_RETURNS sr = (State_RETURNS) st;
				byte[] bytes = DafnySequence.toByteArray((DafnySequence<Byte>) sr.data);
				end(bytes,BigInteger.ZERO);
			} else if(st instanceof State_REVERTS) {
				State_REVERTS sr = (State_REVERTS) st;
				byte[] bytes = DafnySequence.toByteArray((DafnySequence<Byte>) sr.data);
				revert(bytes,BigInteger.ZERO);
			} else {
				exception(BigInteger.ZERO);
			}
		}

		public abstract void step(SnapShot state);

		public abstract void end(byte[] output, BigInteger gasUsed);

		public abstract void revert(byte[] output, BigInteger gasUsed);

		public abstract void exception(BigInteger gasUsed);
	}

}
