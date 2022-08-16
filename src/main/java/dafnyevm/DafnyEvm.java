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

import static EvmBerlin_Compile.__default.Create;
import static EvmBerlin_Compile.__default.Execute;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import EvmState_Compile.State;
import EvmState_Compile.State_CALLS;
import EvmState_Compile.State_INVALID;
import EvmState_Compile.State_OK;
import EvmState_Compile.State_RETURNS;
import EvmState_Compile.State_REVERTS;
import dafny.DafnyMap;
import dafny.DafnySequence;
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
	 * A default tracer which does nothing.
	 */
	public static final Tracer DEFAULT_TRACER = (ctx, st) -> {
	};
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
	 * Gas price to use.
	 */
	private BigInteger gasPrice;

	/**
	 * Construct a Dafny Evm with a given initial storage and bytecode sequence.
	 *
	 * @param storage
	 * @param code
	 */
	public DafnyEvm(Map<BigInteger,BigInteger> storage, byte[] code) {
		this.storage = new DafnyMap<>(storage);
		this.code = DafnySequence.fromBytes(code);
		this.gasPrice = BigInteger.ONE;
	}

	/**
	 * Set the gas price to use when executing transactions.
	 *
	 * @param gasPrice
	 * @return
	 */
	public DafnyEvm setGasPrice(BigInteger gasPrice) {
		this.gasPrice = gasPrice;
		return this;
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
	 * @param to       The receiving account.
	 * @param from     The externally owned account.
	 * @param gasLimit Amount of gas to provide.
	 * @param callValue Amout of Wei to deposit.
	 * @param calldata Input supplied with the call.
	 * @return
	 */
	public Outcome call(BigInteger to, BigInteger from, BigInteger gasLimit, BigInteger callValue, byte[] calldata) {
		// Create call context.
		Context_Compile.Raw ctx = Context_Compile.__default.Create(to, from, callValue,
				DafnySequence.fromBytes(calldata), gasPrice);
		// Create the EVM
		EvmState_Compile.State r = Create(ctx, storage, gasLimit, code);
		// Execute it!
		return Outcome.from(tracer, ctx, r).run();
	}

	/**
	 * Represents the various possible outcomes after executing a given code
	 * sequence on this EVM. In effect, it is a wrapper for the Dafny data type
	 * <code>EvmState.State</code>. A key objective of this class is to isolate all
	 * of the Dafny specific data types from the rest of the codebase.
	 *
	 * @author David J. Pearce
	 *
	 */
	public abstract static class Outcome {
		protected final Tracer tracer;
		/**
		 * Raw EVM context
		 */
		protected final Context_Compile.Raw context;
		/**
		 * State of the EVM (so we can query it).
		 */
		protected final EvmState_Compile.State state;

		public Outcome(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
			this.tracer = tracer;
			this.context = context;
			this.state = state;
		}

		public byte[] getReturnData() { return null; }

		/**
		 * Execute dafny EVM until it reaches a terminal (or continuation) state.
		 *
		 * @param ctx
		 * @param r
		 * @return
		 */
		protected Outcome run() {
			// Execute it!
			tracer.step(context, state);
			EvmState_Compile.State r = Execute(state);
			// Continue whilst the EVM is happy.
			while (r instanceof State_OK) {
				tracer.step(context, r);
				r = Execute(r);
			}
			// Final step
			tracer.step(context, r);
			// Done
			return from(tracer, context, r);
		}

		/**
		 * Construct an appropriate wrapper from an internal Dafny EVM state.
		 *
		 * @param state
		 * @return
		 */
		public static Outcome from(Tracer tracer, Context_Compile.Raw context, State state) {
			if (state instanceof State_INVALID) {
				return new Outcome.Invalid(tracer, context, state);
			} else if (state instanceof State_OK) {
				return new Outcome.Ok(tracer, context, state);
			} else if (state instanceof State_REVERTS) {
				return new Outcome.Revert(tracer, context, state);
			} else if (state instanceof State_RETURNS) {
				return new Outcome.Return(tracer, context, state);
			} else {
				return new Outcome.Call(tracer, context, state);
			}
		}

		/**
		 * Indicates the EVM is running normally.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Ok extends Outcome {
			public Ok(Tracer tracer, Context_Compile.Raw context, State state) {
				super(tracer, context, state);
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
				return sok.Decode() & 0xff;
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
			 * Get the state of the storage when the machine halted.
			 *
			 * @return
			 */
			public Map<BigInteger,BigInteger> getStorage() {
				State_OK sok = (State_OK) state;
				DafnyMap<? extends BigInteger, ? extends BigInteger> m = sok.evm.storage.contents;
				HashMap<BigInteger,BigInteger> storage = new HashMap<>();
				m.forEach((k,v) -> storage.put(k,v));
				System.out.println("GOT: " + storage);
				return storage;
			}

			/**
			 * Get the state of memory at this point in time.
			 *
			 * @return
			 */
			public byte[] getMemory() {
				State_OK sok = (State_OK) state;
				DafnySequence bytes = sok.evm.memory.contents;
				return DafnySequence.toByteArray(bytes);
			}

			/**
			 * Get the current size of memory (in bytes).
			 *
			 * @return
			 */
			public int getMemorySize() {
				State_OK sok = (State_OK) state;
				return sok.evm.memory.contents.length();
			}

			/**
			 * Get the state of the stack when the machine halted.
			 *
			 * @return
			 */
			public BigInteger[] getStack() {
				State_OK sok = (State_OK) state;
				DafnySequence<? extends BigInteger> dStack = sok.evm.stack.contents;
				BigInteger[] rStack = new BigInteger[dStack.length()];
				final int n = rStack.length;
				// NOTE: this is necessary because the stack is actually maintained "backwards"
				// inside the Dafny EVM. Potentially, it might make sense to change that at some
				// point.
				for(int i=0;i!=n;++i) {
					rStack[i] = dStack.select(n - (i+1));
				}
				return rStack;
			}
		}

		/**
		 * Indicates a <code>REVERT</code> occurred producing zero or more bytes of
		 * return data.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Revert extends Outcome {
			public Revert(Tracer tracer, Context_Compile.Raw context, State state) {
				super(tracer, context, state);
			}

			/**
			 * Get any return data from this contract call.
			 *
			 * @return
			 */
			@Override
			public byte[] getReturnData() {
				State_REVERTS sr = (State_REVERTS) state;
				return DafnySequence.toByteArray(((DafnySequence) sr.data));
			}

			public BigInteger getGasUsed() {
				// TODO: fixme!
				return BigInteger.ZERO;
			}
		}

		/**
		 * Indicates a <code>RETURN</code> occurred producing zero or more bytes of
		 * return data.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Return extends Outcome {
			public Return(Tracer tracer, Context_Compile.Raw context, State state) {
				super(tracer, context, state);
			}
			/**
			 * Get any return data from this contract call.
			 *
			 * @return
			 */
			@Override
			public byte[] getReturnData() {
				State_RETURNS sr = (State_RETURNS) state;
				return DafnySequence.toByteArray(((DafnySequence) sr.data));
			}

			public BigInteger getGasUsed() {
				// TODO: fixme!
				return BigInteger.ZERO;
			}
		}

		/**
		 * Indicates an exception occurred for some reason (e.g. <i>stack underflow</i>,
		 * <i>out-of-gas</i>, etc.).
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Invalid extends Outcome {
			public Invalid(Tracer tracer, Context_Compile.Raw context, State state) {
				super(tracer, context,state);
			}

			public BigInteger getGasUsed() {
				// TODO: fixme!
				return BigInteger.ZERO;
			}
		}

		/**
		 * Indicates a <code>CALL</code> occurred, meaning that execution should
		 * continue after the call is made (i.e. this is a continuation).
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Call extends Outcome {
			public Call(Tracer tracer, Context_Compile.Raw context, State state) {
				super(tracer, context, state);
			}

			public BigInteger receiver() {
				State_CALLS st = (State_CALLS) state;
				return st.to;
			}

			/**
			 * Continue this continuation.
			 *
			 * @return
			 */
			public Outcome callContinue() {
				return run();
			}
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
		public void step(Context_Compile.Raw context, EvmState_Compile.State st);
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
		public final void step(Context_Compile.Raw context, EvmState_Compile.State st) {
			if(st instanceof State_OK) {
				step(new Outcome.Ok(this, context, st));
			} else if(st instanceof State_RETURNS) {
				end(new Outcome.Return(this, context,st));
			} else if(st instanceof State_REVERTS) {
				revert(new Outcome.Revert(this, context,st));
			} else {
				exception(new Outcome.Invalid(this, context,st));
			}
		}

		public abstract void step(Outcome.Ok state);

		public abstract void end(Outcome.Return state);

		public abstract void revert(Outcome.Revert state);

		public abstract void exception(Outcome.Invalid state);
	}

}
