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

import EVM_Compile.Result;
import EVM_Compile.Result_INVALID;
import EVM_Compile.Result_OK;
import EVM_Compile.Result_RETURNS;
import EVM_Compile.Result_REVERT;
import dafny.DafnyMap;
import dafny.DafnySequence;


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
	public State call(BigInteger from, byte[] calldata) {
		// Create call context.
		Context_Compile.Raw ctx = Context_Compile.__default.create(from, DafnySequence.fromBytes(calldata));
		// Create the EVM
		EVM_Compile.T evm = create(ctx, storage, BigInteger.ONE, code);
		// Execute it!
		Result r = execute(evm);
		// Continue whilst the EVM is happy.
		while(r instanceof Result_OK) {
			tracer.step(evm);
			Result_OK rok = (Result_OK) r;
			evm = rok.evm;
			r = execute(evm);
		}
		// Decide what happened
		if(r instanceof Result_RETURNS) {
			Result_RETURNS rret = (Result_RETURNS) r;
			return new State(false,rret.data,rret.gas,evm);
		} else if(r instanceof Result_REVERT) {
			Result_REVERT rrev = (Result_REVERT) r;
			return new State(true,rrev.data,rrev.gas,evm);
		} else {
			// Sanity check is invalid
			Result_INVALID rinv = (Result_INVALID) r;
			return new State(false,null,null,evm);
		}
	}

	/**
	 * A simple class capturing the output of an execution, including the full
	 * machine state.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class State {
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

		public State(EVM_Compile.T state) {
			this(false,null,null,state);
		}

		public State(boolean revert, DafnySequence<? extends Byte> data, BigInteger gas, EVM_Compile.T state) {
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
		 * Get the state of the memory when the machine halted.
		 *
		 * @return
		 */
		public DafnyMap<? extends BigInteger,? extends Byte> getMemory() {
			return state.memory.contents;
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
	}

	/**
	 * The default tracer does nothing at all.
	 */
	public static final Tracer DEFAULT_TRACER = new Tracer() {

		@Override
		public void step(EVM_Compile.T evm) {

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
			this.step(new State(evm));
		}

		public abstract void step(State state);
	}

}
