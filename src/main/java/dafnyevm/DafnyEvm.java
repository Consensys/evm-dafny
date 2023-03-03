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

import static EvmBerlin_Compile.__default.Execute;

import java.math.BigInteger;

import org.apache.commons.lang3.tuple.Pair;
import org.web3j.crypto.Hash;
import org.web3j.rlp.RlpEncoder;
import org.web3j.rlp.RlpList;
import org.web3j.rlp.RlpString;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import EvmState_Compile.Continuation_CALLS;
import EvmState_Compile.Continuation_CREATES;
import EvmState_Compile.State_CONTINUING;
import EvmState_Compile.State_INVALID;
import EvmState_Compile.State_EXECUTING;
import EvmState_Compile.State_RETURNS;
import EvmState_Compile.State_REVERTS;
import WorldState_Compile.Account;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.Tuple2;
import evmtools.core.LegacyTransaction;
import evmtools.core.Transaction;
import evmtools.core.Transaction.Outcome;
import evmtools.util.Hex;
import dafnyevm.util.Errors;
import dafnyevm.util.Word.Uint160;
import dafnyevm.util.Word.Uint256;

/**
 * An API which wraps the Dafny-generated classes to interacting with the Dafny
 * EVM simpler.
 *
 * @author David J. Pearce
 *
 */
public class DafnyEvm {
    /**
     * Extract the maximum permitted code size from Dafny,
     */
    private static final int MAX_CODE_SIZE = Code_Compile.__default.MAX__CODE__SIZE().intValueExact();
	/**
	 * A default tracer which does nothing.
	 */
	public static final Tracer DEFAULT_TRACER = new Tracer() {
        @Override
        public void step(int depth, EvmState_Compile.State_EXECUTING st) {}

        @Override
        public void enter(EvmState_Compile.State st) {}

        @Override
        public void leave(int depth, EvmState_Compile.State st) {}
	};
	/**
	 * Tracer is used for monitoring EVM state during execution.
	 */
	private Tracer tracer = DEFAULT_TRACER;
	/**
	 * World state to use for this call.
	 */
	private DafnyMap<BigInteger, Account> worldState = new DafnyMap<>();
	/**
	 * Current block information.
	 */
	private BlockInfo blockInfo = new BlockInfo();

	/**
	 * Set the tracer to use during execution of this EVM. Tracers provide a
	 * mechanism for profiling execution of the EVM, and looking at internal states
	 * during the execution.
	 *
	 * @param tracer
	 * @return
	 */
	public DafnyEvm tracer(Tracer tracer) {
		this.tracer = tracer;
		return this;
	}

	/**
	 * Set the block info to use when executing transactions.
	 *
	 * @param gasPrice
	 * @return
	 */
	public DafnyEvm blockInfo(BlockInfo info) {
		this.blockInfo = info;
		return this;
	}

    /**
     * Calculate the intrisinc gas required for the transaction as it currently
     * stands.
     */
	public BigInteger getIntrinsicGas(Transaction tx) {
        // NOTE: these constants are to be deprecated ASAP by moving the logic for
        // intrinsic gas into the Dafny side.
	    final BigInteger G_txdatazero = BigInteger.valueOf(4);
	    final BigInteger G_txdatanonzero = BigInteger.valueOf(16);
	    final BigInteger G_txcreate = BigInteger.valueOf(32000);
	    final BigInteger G_transaction = BigInteger.valueOf(21000);
	    final byte[] callData = tx.data();
	    //
	    BigInteger gas = BigInteger.ZERO;
	    for(int i=0;i!=callData.length;++i) {
	        if(callData[i] == 0) {
	            gas = gas.add(G_txdatazero);
	        } else {
	            gas = gas.add(G_txdatanonzero);
	        }
	    }
	    //
	    if(tx.to() == null) {
	        gas = gas.add(G_txcreate);
	    }
	    //
	    gas = gas.add(G_transaction);
	    //
	    return gas;
	}

	/**
	 * Create a new account at a given address.
	 *
	 * @param address
	 * @param account
	 * @return
	 */
	public DafnyEvm create(BigInteger address, byte[] bytecode) {
		return create(address, BigInteger.ZERO, BigInteger.ZERO, Collections.emptyMap(), bytecode);
	}

	public DafnyEvm create(BigInteger address, BigInteger balance) {
		return create(address, BigInteger.ZERO, balance, Collections.emptyMap(), new byte[0]);
	}

	public DafnyEvm create(BigInteger address, BigInteger nonce, BigInteger endowment, Map<BigInteger, BigInteger> storage, byte[] bytecode) {
		DafnyMap<BigInteger,BigInteger> store = new DafnyMap<BigInteger,BigInteger>(storage);
		DafnySequence<Byte> code = DafnySequence.fromBytes(bytecode);
		WorldState_Compile.Account acct = WorldState_Compile.__default.CreateAccount(nonce, endowment, store,code);
		this.worldState = DafnyMap.update(worldState, address, acct);
		return this;
	}

    /**
     * Attempt to execute a transaction on the network.
     *
     * @param tx
     * @return
     */
	public DafnyEvm.State<?> execute(Transaction tx) {
	       // Construct world state and substate
        WorldState_Compile.T ws = WorldState_Compile.__default.Create(worldState);
        SubState_Compile.Raw ss = SubState_Compile.__default.Create();
        EvmState_Compile.State st;
	    // Perform initial checks
	    BigInteger intrinsic = getIntrinsicGas(tx);
	    BigInteger gasPrice;

	    if (tx.gasLimit().compareTo(intrinsic) < 0) {
            return new State.Invalid(tracer,Transaction.Outcome.INTRINSIC_GAS);
        } else if(!(tx instanceof LegacyTransaction)) {
            return new State.Invalid(tracer,Transaction.Outcome.TYPE_NOT_SUPPORTED);
        } else {
            LegacyTransaction ltx = (LegacyTransaction) tx;
            gasPrice = ltx.gasPrice();
            BigInteger cost = ltx.gasLimit().multiply(ltx.gasPrice());
            BigInteger balance = worldState.get(ltx.sender()).dtor_balance();
            //
            if(cost.compareTo(balance) > 0) {
                return new State.Invalid(tracer,Transaction.Outcome.INSUFFICIENT_FUNDS);
            } else {
                // Pay for transaction execution
                ws = ws.Withdraw(ltx.sender(), cost);
            }
        }
	    // Increment sender's nonce
	    ws = ws.IncNonce(tx.sender());
	    // Calculate starting gas
	    BigInteger gas = tx.gasLimit().subtract(intrinsic);
	    // Setup transaction executor
	    DafnySequence<Byte> callData = DafnySequence.fromBytes(tx.data());
	    // Decide between call and create
	    if(tx.to() != null) {
	        // Contract call
	        Context_Compile.T ctx = Context_Compile.__default.Create(tx.sender(), tx.sender(), tx.to(), tx.value(),
	                callData, true, gasPrice, blockInfo.toDafny());
	        // Mark sender + recipient as having being accessed
	        ss = ss.AccountAccessed(tx.sender());
	        ss = ss.AccountAccessed(tx.to());
	        // Begin the call.
	        st = EvmState_Compile.__default.Call(ws, ctx, ss, tx.to(), tx.value(), gas,
	                BigInteger.ONE);
	    } else {
	        // Contract creation
	        // Determine sender's nonce
	        BigInteger nonce = worldState.get(tx.sender()).dtor_nonce();
	        // NOTE: we do not subtract one from the nonce here, as this address is being
	        // calculated *before* the sender's nonce is incremented.
	        BigInteger address = addr(tx.sender(),nonce);
	        // Construct the transaction context for the call.
	        Context_Compile.T ctx = Context_Compile.__default.Create(tx.sender(), tx.sender(), address, tx.value(),
	                DafnySequence.fromBytes(new byte[0]), true, gasPrice, blockInfo.toDafny());
	        // Begin the call.
	        st = EvmState_Compile.__default.Create(ws, ctx, ss, callData, gas, BigInteger.ONE);
	    }
	    // Execute bytecodes!
	    if(st instanceof State_EXECUTING) {
	        st = run(tx, 0, tracer, (State_EXECUTING) st);
	        // Sanity check returned contract code (for contract creation)
	        if (tx.to() == null && st.is_RETURNS()) {
	            State_RETURNS rst = (State_RETURNS) st;
	            // Sanity check contract size
	            if (rst.dtor_data().length() > MAX_CODE_SIZE) {
	                // Contract being created is too large.
	                EvmState_Compile.Error err = EvmState_Compile.Error.create_CODESIZE__EXCEEDED();
	                st = EvmState_Compile.State.create_INVALID(err);
	            }
	        }
	    }
	    // NOTE: should refund unused gas?
	    // Convert back into the Java API
	    return State.from(0,tracer,st);
	}

	/**
	 * Execute dafny EVM until it reaches a terminal (or continuation) state.
	 *
	 * @param tracer  Tracer to use for generating debug information (if required).
	 * @param context Enclosing Dafny context.
	 * @param state   Current DafnyEvm state.
	 * @return
	 */
    protected static EvmState_Compile.State run(Transaction tx, int depth, Tracer tracer, State_EXECUTING _st) {
        EvmState_Compile.State st = _st;
        tracer.enter(st);
        // Continue whilst the EVM is happy.
        while (st.is_EXECUTING()) {
            tracer.step(depth, (EvmState_Compile.State_EXECUTING) st);
            st = Execute(st);
            // Manage continuations
            if (st.is_CONTINUING()) {
                EvmState_Compile.Continuation cc = ((State_CONTINUING) st)._a0;
                if (cc.is_CALLS()) {
                    st = callContinue(tx, depth, tracer, (Continuation_CALLS) cc);
                } else {
                    st = createContinue(tx, depth, tracer, (Continuation_CREATES) cc);
                }
            }
        }
        // Final step
        tracer.leave(depth, st);
        //
        return st;
    }

	/**
	 * Manage a nested contract call. This creates a child EVM to execute the
	 * contract code, and then marshalls the return data back from that (along with
	 * other things, like the logs).
	 *
	 * @param cc    The continuation state.
	 * @param depth The current call depth.
	 * @return
	 */
	private static EvmState_Compile.State callContinue(Transaction tx, int depth, Tracer tracer, EvmState_Compile.Continuation_CALLS cc) {
	    // Sanity check precondition for CallEnter
        if(!cc.dtor_evm().dtor_world().Exists(cc._sender)) {
            throw new IllegalArgumentException("Non-existent sender account!");
        }
	    //
		EvmState_Compile.State st = cc.CallEnter(BigInteger.valueOf(depth));
		//
		if(st instanceof State_EXECUTING) {
		    // Run code within recursive call.
		    st = run(tx, depth + 1, tracer, (State_EXECUTING) st);
		}
	    // Return from call.
	    return cc.CallReturn(st);
	}

	/**
	 * Manage a nested contract creation.
	 *
	 * @param cc    The continuation state.
	 * @param depth The current call depth.
	 * @return
	 */
	private static EvmState_Compile.State createContinue(Transaction tx, int depth, Tracer tracer, EvmState_Compile.Continuation_CREATES cc) {
		// Determine sender
		BigInteger sender = cc.dtor_evm().dtor_context().dtor_address();
		// Construct new account
		Account acct = cc.dtor_evm().dtor_world().dtor_accounts().get(sender);
		// Subtract one from nonce (i.e. because it was already incremented prior to this point)
		BigInteger nonce = acct.dtor_nonce().subtract(BigInteger.ONE);
		// NOTE: we do not subtract one from the nonce here, as this address is being
		// calculated *before* the sender's nonce is incremented.
		byte[] hash = addr(sender, nonce, cc.dtor_salt(), cc.dtor_initcode());
		// Finally reconstruct the address from the rightmost 160bits.
		BigInteger address = new BigInteger(1, hash);
		// Begin the recursive call.
		EvmState_Compile.State st = cc.CreateEnter(BigInteger.valueOf(depth), address, cc.dtor_initcode());
		// Run init code for recursive call.
		if(st instanceof State_EXECUTING) {
		    st = run(tx, depth + 1, tracer, (State_EXECUTING) st);
		}
		// Return from creation
		return cc.CreateReturn(st, address);
	}

	/**
	 * Programmatically construct a contract addres from the various key
	 * ingredients.
	 *
	 * @param sender   The sender address.
	 * @param nonce    The sender's account nonce.
	 * @return
	 */
	public static BigInteger addr(BigInteger sender, BigInteger nonce) {
		byte[] hash = addr(sender,nonce,new Optional_Compile.Option_None<>(),null);
		return new BigInteger(1,hash);
	}

	/**
	 * Programmatically construct a contract addres from the various key
	 * ingredients. This is the <code>ADDR</code> function defined in the yellow
	 * paper.
	 *
	 * @param sender   The sender address.
	 * @param nonce    The sender's account nonce.
	 * @param salt     An optional salt value (for CREATE2).
	 * @param initCode The initialisation code (only used with salt).
	 * @return
	 */
	public static byte[] addr(BigInteger sender, BigInteger nonce, Optional_Compile.Option<BigInteger> salt,
			DafnySequence<? extends Byte> initCode) {
		byte[] bytes;
		//
		if (salt instanceof Optional_Compile.Option_None) {
			// Case for CREATE
			bytes = new Uint160(sender).getBytes();
			bytes = RlpEncoder.encode(new RlpList(RlpString.create(bytes),RlpString.create(nonce)));
		} else {
			@SuppressWarnings({ "rawtypes", "unchecked" })
			byte[] code = DafnySequence.toByteArray((DafnySequence) initCode);
			Optional_Compile.Option_Some<BigInteger> s = (Optional_Compile.Option_Some<BigInteger>) salt;
			// Case for CREATE2 (see EIP 1014).
			byte ff = (byte) (0xff & 0xff);
			byte[] senderBytes = new Uint160(sender).getBytes();
			byte[] saltBytes = new Uint256(s.dtor_v()).getBytes();
			bytes = concat(new byte[] { ff }, senderBytes, saltBytes, Hash.sha3(code));
		}
		// Calculate hash.
		byte[] hash = Hash.sha3(bytes);
		return Arrays.copyOfRange(hash, 12, hash.length);
	}

	/**
	 * Concatenate zero or more byte arrays together.
	 *
	 * @param arrays
	 * @return
	 */
	private static byte[] concat(byte[]... arrays) {
		int n = 0;
		for (int i = 0; i != arrays.length; ++i) {
			n += arrays[i].length;
		}
		byte[] result = new byte[n];
		int index = 0;
		for (int i = 0; i != arrays.length; ++i) {
			byte[] ith = arrays[i];
			System.arraycopy(ith, 0, result, index, ith.length);
			index += ith.length;
		}
		return result;
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
	public abstract static class State<T extends EvmState_Compile.State> {
		protected final Tracer tracer;
		/**
		 * State of the EVM (so we can query it).
		 */
		protected final T state;
		/**
		 * Level of nesting for contract calls.
		 */
		protected final int depth;

		public State(Tracer tracer, T state, int depth) {
			this.tracer = tracer;
			this.state = state;
			this.depth = depth;
		}

		public abstract byte[] getReturnData();

		public abstract Transaction.Outcome getOutcome();

        /**
         * Get gas remaining.
         *
         * @return
         */
	    public abstract BigInteger getGas();

		public Pair<BigInteger[], byte[]>[] getLog() {
			throw new IllegalArgumentException("log not available in state " + this.getClass().getName());
		}

		public int getDepth() { return depth; }

		/**
		 * Construct an appropriate wrapper from an internal Dafny EVM state.
		 *
		 * @param state
		 * @return
		 */
		public static State<?> from(int depth, Tracer tracer, EvmState_Compile.State state) {
			if (state instanceof State_INVALID) {
				return new State.Exception(tracer, (State_INVALID) state, depth);
			} else if (state instanceof State_EXECUTING) {
				return new State.Executing(tracer, (State_EXECUTING) state, depth);
			} else if (state instanceof State_REVERTS) {
				return new State.Revert(tracer, (State_REVERTS) state, depth);
			} else if (state instanceof State_RETURNS) {
				return new State.Return(tracer, (State_RETURNS) state, depth);
			} else {
				throw new IllegalArgumentException("invalid state encountered (" + state.getClass().getName() + ")");
			}
		}

		/**
		 * Abstract class capturing things common to the two running EVM states.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static abstract class Running<T extends EvmState_Compile.State> extends State<T> {
			public Running(Tracer tracer, T state, int depth) {
				super(tracer, state, depth);
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
			@Override
            public BigInteger getGas() {
				return getEVM().dtor_gas();
			}

			/**
			 * Get current <code>pc</code> value.
			 */
			public BigInteger getPC() {
				return getEVM().dtor_pc();
			}

			/**
			 * Get the state of memory at this point in time.
			 *
			 * @return
			 */
			@SuppressWarnings("unchecked")
			public byte[] getMemory() {
				@SuppressWarnings("rawtypes")
				DafnySequence bytes = getEVM().dtor_memory();
				return DafnySequence.toByteArray(bytes);
			}

			/**
			 * Get the current size of memory (in bytes).
			 *
			 * @return
			 */
			public int getMemorySize() {
				return getEVM().dtor_memory().length();
			}

			/**
			 * Get the state of the stack when the machine halted.
			 *
			 * @return
			 */
			public BigInteger[] getStack() {
				DafnySequence<? extends BigInteger> dStack = getEVM().dtor_stack();
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
			 * Get the state of the storage (for the executing account) when the machine halted.
			 *
			 * @return
			 */
			public Map<BigInteger,BigInteger> getStorage() {
				HashMap<BigInteger,BigInteger> storage = new HashMap<>();
				// Determine executing account address
				BigInteger address = getEVM().dtor_context().dtor_address();
				// Get account record
				WorldState_Compile.Account a = getEVM().dtor_world().dtor_accounts().get(address);
				// Extract storage
				DafnyMap<? extends BigInteger, ? extends BigInteger> m = a.dtor_storage();
				// Copy over
				m.forEach((k,v) -> storage.put(k,v));
				return storage;
			}

			/**
			 * Extract internal EVM state.
			 * @return
			 */
			protected abstract EvmState_Compile.Raw getEVM();
		}

		/**
		 * Indicates the EVM is running normally.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Executing extends Running<State_EXECUTING> {
			public Executing(Tracer tracer, State_EXECUTING state, int depth) {
				super(tracer, state, depth);
			}

			@Override
			protected EvmState_Compile.Raw getEVM() {
				return state.dtor_evm();
			}

			public Map<BigInteger,evmtools.core.Account> getWorldState() {
				return toWorldState(getEVM().dtor_world());
			}

			@Override
			public String toString() {
				String ws = toWorldStateString(getWorldState());
				// FIXME: might want to add more stuff here at some point!
				return "OK(" + ws + ")";
			}

            @Override
            public byte[] getReturnData() {
                throw new UnsupportedOperationException();
            }

            @Override
            public Transaction.Outcome getOutcome() {
                throw new UnsupportedOperationException();
            }
		}

		/**
		 * Indicates a <code>REVERT</code> occurred producing zero or more bytes of
		 * return data.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Revert extends State<State_REVERTS> {
			public Revert(Tracer tracer, State_REVERTS state, int depth) {
				super(tracer, state, depth);
			}

			/**
			 * Get any return data from this contract call.
			 *
			 * @return
			 */
			@SuppressWarnings("unchecked")
			@Override
			public byte[] getReturnData() {
				@SuppressWarnings("rawtypes")
				DafnySequence data = (DafnySequence) state.dtor_data();
				return DafnySequence.toByteArray(data);
			}

			@Override
            public BigInteger getGas() {
				return state.dtor_gas();
			}

            @Override
            public Transaction.Outcome getOutcome() {
                return Transaction.Outcome.REVERT;
            }
		}

		/**
		 * Indicates a <code>RETURN</code> occurred producing zero or more bytes of
		 * return data.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Return extends State<State_RETURNS> {
			public Return(Tracer tracer, State_RETURNS state, int depth) {
				super(tracer, state, depth);
			}
			/**
			 * Get any return data from this contract call.
			 *
			 * @return
			 */
			@SuppressWarnings("unchecked")
			@Override
			public byte[] getReturnData() {
				@SuppressWarnings("rawtypes")
				DafnySequence data = (DafnySequence) state.dtor_data();
				return DafnySequence.toByteArray(data);
			}

			@Override
            public BigInteger getGas() {
				return state.dtor_gas();
			}

			public Map<BigInteger,evmtools.core.Account> getWorldState() {
				return toWorldState(state.dtor_world());
			}

            @Override
            public Transaction.Outcome getOutcome() {
                return Transaction.Outcome.RETURN;
            }
			/**
			 * Get the log returned from this running the call.
			 *
			 * @return
			 */
			@SuppressWarnings({ "rawtypes", "unchecked" })
			@Override
			public Pair<BigInteger[], byte[]>[] getLog() {
				DafnySequence<? extends Tuple2> dlog = state.dtor_substate().dtor_log();
				Pair<BigInteger[], byte[]>[] log = new Pair[dlog.length()];
				for (int i = 0; i != log.length; ++i) {
					Tuple2<DafnySequence<BigInteger>, DafnySequence<Byte>> ith = dlog.select(i);
					BigInteger[] topics = (BigInteger[]) ith.dtor__0().toRawArray();
					byte[] data = DafnySequence.toByteArray(ith.dtor__1());
					log[i] = Pair.of(topics, data);
				}
				//
				return log;
			}

			@Override
			public String toString() {
				String ws = toWorldStateString(getWorldState());
				return "RETURN(gas=" + getGas() + "," + Hex.toHexString(getReturnData()) + "," + ws + ")";
			}
		}

		/**
         * Indicates an invalid transaction was submitted for execution (which returned
         * immediately).
         *
         * @author David J. Pearce
         *
         */
		public static class Invalid extends State<State_INVALID> {
		    private final Transaction.Outcome cause;

		    public Invalid(Tracer tracer, Transaction.Outcome cause) {
		        super(tracer,null,0);
		        this.cause = cause;
		    }

            @Override
            public Transaction.Outcome getOutcome() {
                return cause;
            }

            @Override
            public BigInteger getGas() {
                throw new UnsupportedOperationException();
            }

            @Override
            public byte[] getReturnData() {
                return new byte[0];
            }
		}

		/**
		 * Indicates an exception occurred for some reason (e.g. <i>stack underflow</i>,
		 * <i>out-of-gas</i>, etc.).
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Exception extends State<State_INVALID> {
			public Exception(Tracer tracer, State_INVALID state, int depth) {
				super(tracer, state, depth);
			}

			/**
			 * Return the error code associated with this exception.
			 *
			 * @return
			 */
            @Override
            public Transaction.Outcome getOutcome() {
                return Errors.toErrorCode(state._a0);
            }

			@Override
            public BigInteger getGas() {
				return BigInteger.ZERO;
			}

			@Override
            public byte[] getReturnData() {
                return new byte[0];
            }

			@Override
			public String toString() {
				return "Invalid(" + state._a0.getClass().getSimpleName() + ")";
			}
		}

		private static Map<BigInteger, evmtools.core.Account> toWorldState(WorldState_Compile.T world) {
			DafnyMap<? extends BigInteger, ? extends Account> accounts = world.dtor_accounts();
			HashMap<BigInteger, evmtools.core.Account> ws = new HashMap<>();
			for (BigInteger account : accounts.keySet().Elements()) {
				Account a = accounts.get(account);
				@SuppressWarnings({ "rawtypes", "unchecked" })
				byte[] bytecode = DafnySequence.toByteArray((DafnySequence) a.dtor_code());
				Map<BigInteger, BigInteger> store = new HashMap<>();
				DafnyMap<? extends BigInteger, ? extends BigInteger> m = a.dtor_storage();
				// Copy over
				m.forEach((k, v) -> store.put(k, v));
				ws.put(account, new evmtools.core.Account(a.dtor_balance(), a.dtor_nonce(), store, bytecode));
			}
			return ws;
		}

		private static String toWorldStateString(Map<BigInteger, evmtools.core.Account> world) {
			StringBuilder sb = new StringBuilder();
			sb.append("{");
			boolean firstTime=true;
			for(BigInteger a : world.keySet()) {
				if(!firstTime) {
					sb.append(",");
				}
				firstTime=false;
				sb.append(Hex.toHexString(a));
				sb.append("=");
				sb.append(world.get(a).toString());
			}
			sb.append(")");
			return sb.toString();
		}
	}


	/**
	 * Information about currently block.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class BlockInfo {
		/**
		 * Current block's beneficiary address.
		 */
		public final BigInteger coinBase;
		/**
		 * Current block's timestamp.
		 */
		public final BigInteger timeStamp;
		/**
		 * Current block number.
		 */
		public final BigInteger number;
		/**
		 * Current block's difficulty.
		 */
		public final BigInteger difficulty;
		/**
		 * Current block's gas limit.
		 */
		public final BigInteger gasLimit;
		/**
		 * Current chain ID (Ethereum mainnet == 1).
		 */
		public final BigInteger chainID;

		public BlockInfo() {
			this.coinBase = BigInteger.ONE;
			this.timeStamp = BigInteger.ONE;
			this.number = BigInteger.ONE;
			this.difficulty = BigInteger.ONE;
			this.gasLimit = BigInteger.ONE;
			this.chainID = BigInteger.ONE;
		}

		private BlockInfo(BigInteger coinBase, BigInteger timeStamp, BigInteger number, BigInteger difficulty,
				BigInteger gasLimit, BigInteger chainID) {
			this.coinBase = coinBase;
			this.timeStamp = timeStamp;
			this.number = number;
			this.difficulty = difficulty;
			this.gasLimit = gasLimit;
			this.chainID = chainID;
		}

		/**
		 * Set block's beneficiary address.
		 */
		public BlockInfo coinBase(long v) {
			return this.coinBase(BigInteger.valueOf(v));
		}

		/**
		 * Set block's beneficiary address.
		 */
		public BlockInfo coinBase(BigInteger v) {
			return new BlockInfo(v, timeStamp, number, difficulty, gasLimit, chainID);
		}

		/**
		 * Set block's timestamp.
		 */
		public BlockInfo timeStamp(long v) {
			return this.timeStamp(BigInteger.valueOf(v));
		}

		/**
		 * Set block's timestamp.
		 */
		public BlockInfo timeStamp(BigInteger v) {
			return new BlockInfo(coinBase, v, number, difficulty, gasLimit, chainID);
		}

		/**
		 * Set block's number.
		 */
		public BlockInfo number(long v) {
			return this.number(BigInteger.valueOf(v));
		}

		/**
		 * Set block's number.
		 */
		public BlockInfo number(BigInteger v) {
			return new BlockInfo(coinBase, timeStamp, v, difficulty, gasLimit, chainID);
		}

		/**
		 * Set block's difficulty.
		 */
		public BlockInfo difficulty(long v) {
			return this.difficulty(BigInteger.valueOf(v));
		}

		/**
		 * Set block's difficulty.
		 */
		public BlockInfo difficulty(BigInteger v) {
			return new BlockInfo(coinBase, timeStamp, number, v, gasLimit, chainID);
		}

		/**
		 * Set block's gas limit.
		 */
		public BlockInfo gasLimit(long v) {
			return this.gasLimit(BigInteger.valueOf(v));
		}

		/**
		 * Set block's gas limit.
		 */
		public BlockInfo gasLimit(BigInteger v) {
			return new BlockInfo(coinBase, timeStamp, number, difficulty, v, chainID);
		}

		/**
		 * Set chain ID.
		 */
		public BlockInfo chainID(long v) {
			return this.chainID(BigInteger.valueOf(v));
		}

		/**
		 * Set chain ID.
		 */
		public BlockInfo chainID(BigInteger v) {
			return new BlockInfo(coinBase, timeStamp, number, difficulty, gasLimit, v);
		}

		/**
		 * Convert this object into a Dafny encoding.
		 * @return
		 */
		public Context_Compile.Block toDafny() {
			return new Context_Compile.Block(coinBase, timeStamp, number, difficulty, gasLimit, chainID);
		}
	}

	/**
	 * A tracer is used to extract internal state during execution of the EVM.
	 * @author David J. Pearce
	 *
	 */
	public interface Tracer {
	    /**
	     * Enter a new subtrace (i.e. contract call)
	     */
	    public void enter(EvmState_Compile.State st);
	    /**
         * Enter a new subtrace (i.e. contract call)
         */
        public void leave(int depth, EvmState_Compile.State st);
		/**
		 * Identifies that the EVM has taken a single step of execution (i.e. executed a
		 * bytecode).
		 *
		 * @param evm
		 */
		public void step(int depth, EvmState_Compile.State_EXECUTING st);
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
        public final void enter(EvmState_Compile.State st) {
	        this.enter();
	    }

		@Override
		public final void step(int depth, EvmState_Compile.State_EXECUTING st) {
			step(new State.Executing(this, (State_EXECUTING) st, depth));
		}

		@Override
        public final void leave(int depth, EvmState_Compile.State st) {
            if (st instanceof State_RETURNS) {
                end(new State.Return(this, (State_RETURNS) st, depth));
            } else if (st instanceof State_REVERTS) {
                revert(new State.Revert(this, (State_REVERTS) st, depth));
            } else if (st instanceof State_INVALID) {
                exception(new State.Exception(this, (State_INVALID) st, depth));
            } else  {
                throw new IllegalArgumentException("invalid state encountered (" + st.getClass().getName() + ")");
            }
        }

		public abstract void enter();

		public abstract void step(State.Executing state);

		public abstract void end(State.Return state);

		public abstract void revert(State.Revert state);

		public abstract void exception(State.Exception state);
	}

}
