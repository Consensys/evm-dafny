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

import EvmState_Compile.State_CALLS;
import EvmState_Compile.State_INVALID;
import EvmState_Compile.State_OK;
import EvmState_Compile.State_RETURNS;
import EvmState_Compile.State_REVERTS;
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
	 * Set the tracer to use during execution of this EVM. Tracers provide a
	 * mechanism for profiling execution of the EVM, and looking at internal states
	 * during the execution.
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
	public State call(BigInteger to, BigInteger from, BigInteger gasLimit, BigInteger callValue, byte[] calldata) {
		// Create call context.
		Context_Compile.Raw ctx = Context_Compile.__default.Create(to, from, callValue,
				DafnySequence.fromBytes(calldata), gasPrice);
		// Create initial EVM state
		EvmState_Compile.State st = Create(ctx, storage, gasLimit, code);
		// Execute it!
		return run(tracer,ctx,st);
	}


	/**
	 * Execute dafny EVM until it reaches a terminal (or continuation) state.
	 *
	 * @param tracer  Tracer to use for generating debug information (if required).
	 * @param context Enclosing Dafny context.
	 * @param state   Current DafnyEvm state.
	 * @return
	 */
	protected static State run(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
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
		return State.from(tracer, context, r);
	}

	/**
	 * <p>
	 * Represents the various possible states of the Dafny EVM. In effect, it is a
	 * wrapper for the Dafny data type <code>EvmState.State</code>. A key objective
	 * of this class is to isolate all of the Dafny specific data types from the
	 * rest of the codebase. The states are: <code>Ok</code> (EVM running as
	 * normal); <code>CallContinue</code> (EVM executing a <code>CALL</code>
	 * instruction); <code>Revert</code> (EVM has reverted with returndata);
	 * <code>Returns</code> (EVM has stopped normally with returndata);
	 * <code>Invalid</code> (EVM has encountered an exception, such as stack
	 * underflow, out-of-gas, etc).
	 * </p>
	 * <p>
	 * In the states <code>Ok</code> and <code>CallContinue</code> this can be used
	 * to restart the EVM (e.g. to take another step or sequence of steps, or to
	 * continue after a <code>CALL</code> has completed).
	 * </p>
	 *
	 * @author David J. Pearce
	 *
	 */
	public abstract static class State {
		protected final Tracer tracer;
		/**
		 * Raw EVM context
		 */
		protected final Context_Compile.Raw context;
		/**
		 * State of the EVM (so we can query it).
		 */
		protected final EvmState_Compile.State state;

		public State(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
			this.tracer = tracer;
			this.context = context;
			this.state = state;
		}

		public byte[] getReturnData() { return null; }

		/**
		 * Construct an appropriate wrapper from an internal Dafny EVM state.
		 *
		 * @param state
		 * @return
		 */
		public static State from(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
			if (state instanceof State_INVALID) {
				return new State.Invalid(tracer, context, state);
			} else if (state instanceof State_OK) {
				return new State.Ok(tracer, context, state);
			} else if (state instanceof State_REVERTS) {
				return new State.Revert(tracer, context, state);
			} else if (state instanceof State_RETURNS) {
				return new State.Return(tracer, context, state);
			} else {
				return new State.CallContinue(tracer, context, state);
			}
		}

		/**
		 * Abstract class capturing things common to the two running EVM states.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static abstract class Running extends State {
			public Running(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
				super(tracer, context, state);
			}

			/**
			 * Get current opcode.
			 *
			 * @return
			 */
			public int getOpcode() {
				return state.Decode() & 0xff;
			}

			/**
			 * Get remaining gas.
			 *
			 * @return
			 */
			public BigInteger getRemainingGas() {
				return getEVM().gas;
			}

			/**
			 * Get current <code>pc</code> value.
			 */
			public BigInteger getPC() {
				return getEVM().pc;
			}

			/**
			 * Get the state of the storage when the machine halted.
			 *
			 * @return
			 */
			public Map<BigInteger,BigInteger> getStorage() {
				DafnyMap<? extends BigInteger, ? extends BigInteger> m = getEVM().storage.contents;
				HashMap<BigInteger,BigInteger> storage = new HashMap<>();
				m.forEach((k,v) -> storage.put(k,v));
				return storage;
			}

			/**
			 * Get the state of memory at this point in time.
			 *
			 * @return
			 */
			public byte[] getMemory() {
				DafnySequence bytes = getEVM().memory.contents;
				return DafnySequence.toByteArray(bytes);
			}

			/**
			 * Get the current size of memory (in bytes).
			 *
			 * @return
			 */
			public int getMemorySize() {
				return getEVM().memory.contents.length();
			}

			/**
			 * Get the state of the stack when the machine halted.
			 *
			 * @return
			 */
			public BigInteger[] getStack() {
				DafnySequence<? extends BigInteger> dStack = getEVM().stack.contents;
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

			/**
			 * Extract internal EVM state.
			 * @return
			 */
			protected abstract EvmState_Compile.T getEVM();
		}

		/**
		 * Indicates the EVM is running normally.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Ok extends Running {
			public Ok(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
				super(tracer, context, state);
			}

			@Override
			protected EvmState_Compile.T getEVM() {
				State_OK sok = (State_OK) state;
				return sok.evm;
			}
		}

		/**
		 * Indicates a nested call (either to a contract or an end-user account) has
		 * been initiated. The intention is that the environment manages that call, and
		 * then execution of this state continues after that is finished (i.e. this is a
		 * continuation).
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class CallContinue extends Running {
			public CallContinue(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
				super(tracer, context, state);
			}

			/**
			 * Identify the receiver associated with this call.
			 *
			 * @return
			 */
			public BigInteger receiver() {
				State_CALLS st = (State_CALLS) state;
				return st.to;
			}

			@Override
			protected EvmState_Compile.T getEVM() {
				State_CALLS sok = (State_CALLS) state;
				return sok.evm;
			}

			/**
			 * Continue this continuation.
			 *
			 * @return
			 */
			public State callContinue(boolean success, byte[] returnData) {
				// Determine appropriate exit code.
				BigInteger exitCode = success ? BigInteger.ONE : BigInteger.ZERO;
				// Convert into OK state
				EvmState_Compile.State st = state.CallReturn(exitCode, DafnySequence.fromBytes(returnData));
				// Continue execution.
				return run(tracer, context, st);
			}
		}

		/**
		 * Indicates a <code>REVERT</code> occurred producing zero or more bytes of
		 * return data.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Revert extends State {
			public Revert(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
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
		public static class Return extends State {
			public Return(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
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
		public static class Invalid extends State {
			public Invalid(Tracer tracer, Context_Compile.Raw context, EvmState_Compile.State state) {
				super(tracer, context,state);
			}

			public BigInteger getGasUsed() {
				// TODO: fixme!
				return BigInteger.ZERO;
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
				step(new State.Ok(this, context, st));
			} else if(st instanceof State_RETURNS) {
				end(new State.Return(this, context,st));
			} else if(st instanceof State_REVERTS) {
				revert(new State.Revert(this, context,st));
			} else {
				exception(new State.Invalid(this, context,st));
			}
		}

		public abstract void step(State.Ok state);

		public abstract void end(State.Return state);

		public abstract void revert(State.Revert state);

		public abstract void exception(State.Invalid state);
	}

}
