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
import java.util.Optional;

import org.apache.commons.lang3.tuple.Pair;
import org.web3j.crypto.Hash;
import org.web3j.rlp.RlpEncoder;
import org.web3j.rlp.RlpList;
import org.web3j.rlp.RlpString;

import java.util.Arrays;

import EvmState_Compile.Error_CALLDEPTH__EXCEEDED;
import EvmState_Compile.State_CALLS;
import EvmState_Compile.State_CREATES;
import EvmState_Compile.State_INVALID;
import EvmState_Compile.State_OK;
import EvmState_Compile.State_RETURNS;
import EvmState_Compile.State_REVERTS;
import Log_Compile.Entry;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.Tuple2;
import dafnyevm.util.Hex;
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
	 * A default tracer which does nothing.
	 */
	public static final Tracer DEFAULT_TRACER = (d,st) -> {};
	/**
	 * Default receiver to use for a call (unless otherwise specified).
	 */
	public final static BigInteger DEFAULT_RECEIVER = Hex.toBigInt("0xabc");
	/**
	 * Default origin to use for a call (unless otherwise specified).
	 */
	public final static BigInteger DEFAULT_ORIGIN = Hex.toBigInt("0xdef");
	/**
	 * Default value to deposit for a call (unless otherwise specified).
	 */
	public final static BigInteger DEFAULT_VALUE = BigInteger.ZERO;
	/**
	 * Default gas limit to use for contract calls.
	 */
	public static final BigInteger DEFAULT_GAS = new BigInteger("10000000000");
	/**
	 * Default call data to use for a call (unless otherwise specified).
	 */
	public final static byte[] DEFAULT_DATA = new byte[0];

	/**
	 * Tracer is used for monitoring EVM state during execution.
	 */
	private Tracer tracer = DEFAULT_TRACER;
	/**
	 * World state to use for this call.
	 */
	private Map<BigInteger, Account> worldState = new HashMap<>();
	/**
	 * Initiator of this call, which could be an end-user account or a contract
	 * account.
	 */
	private BigInteger sender = DEFAULT_ORIGIN;
	/**
	 * Receiver of this call, which again could be an end-user account or a contract
	 * account.
	 */
	private BigInteger recipient = DEFAULT_RECEIVER;
	/**
	 * End-user account which initiated the outermost call.
	 */
	private BigInteger origin = DEFAULT_ORIGIN;
	/**
	 * Value to be deposited as part of this call.
	 */
	private BigInteger value = DEFAULT_VALUE;
	/**
	 * Gas provided to execute this call.
	 */
	private BigInteger gas = DEFAULT_GAS;
	/**
	 * Data to be supplied with this call.
	 */
	private byte[] callData = DEFAULT_DATA;
	/**
	 * Gas price to use.
	 */
	private BigInteger gasPrice = BigInteger.ONE;
	/**
	 * Current block information.
	 */
	private BlockInfo blockInfo = new BlockInfo();

	/**
	 * Code to be executed as part of this call. If this is <code>null</code>, then
	 * the receivers code is used by default.
	 */
	private byte[] code = null;

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
	 * Assign a new account to a given address.
	 *
	 * @param address
	 * @param account
	 * @return
	 */
	public DafnyEvm put(BigInteger address, Account account) {
		this.worldState.put(address, account);
		return this;
	}

	/**
	 * Assign zero or more addresses to given accounts.
	 *
	 * @param state
	 * @return
	 */
	public DafnyEvm putAll(Map<BigInteger, Account> state) {
		this.worldState.putAll(state);
		return this;
	}

	/**
	 * Get the sender of this call.
	 *
	 * @return
	 */
	public BigInteger sender() {
		return this.sender;
	}

	/**
	 * Set the sender of this call.
	 *
	 * @param from
	 * @return
	 */
	public DafnyEvm sender(long sender) {
		return sender(BigInteger.valueOf(sender));
	}

	/**
	 * Set the sender of this call.
	 *
	 * @param from
	 * @return
	 */
	public DafnyEvm sender(BigInteger sender) {
		this.sender = sender;
		return this;
	}

	/**
	 * Set the receiver of this calln.
	 *
	 * @param from
	 * @return
	 */
	public DafnyEvm to(long to) {
		return to(BigInteger.valueOf(to));
	}

	/**
	 * Set the receiver of this calln.
	 *
	 * @param from
	 * @return
	 */
	public DafnyEvm to(BigInteger to) {
		this.recipient = to;
		return this;
	}

	/**
	 * Get the origin of the enclosing transaction. That may be the same as the
	 * receiver (if the call depth is <code>0</code>), or not (if the call depth is
	 * not <code>0</code>).
	 *
	 * @return
	 */
	public BigInteger origin() {
		return origin;
	}

	/**
	 * Set the origin of the enclosing transaction.
	 *
	 * @param origin
	 * @return
	 */
	public DafnyEvm origin(long origin) {
		return origin(BigInteger.valueOf(origin));
	}

	/**
	 * Set the origin of the enclosing transaction.
	 *
	 * @param origin
	 * @return
	 */
	public DafnyEvm origin(BigInteger origin) {
		this.origin = origin;
		return this;
	}

	/**
	 * Get the value to be deposited by this call.
	 *
	 * @param value
	 * @return
	 */
	public DafnyEvm value(long value) {
		return value(BigInteger.valueOf(value));
	}

	/**
	 * Set the value to be deposited by this call.
	 *
	 * @param value
	 * @return
	 */
	public DafnyEvm value(BigInteger value) {
		this.value = value;
		return this;
	}

	/**
	 * Get the gas limit for this call.
	 *
	 * @param value
	 * @return
	 */
	public DafnyEvm gas(long gas) {
		return gas(BigInteger.valueOf(gas));
	}

	/**
	 * Set the gas limit for this call.
	 *
	 * @param value
	 * @return
	 */
	public DafnyEvm gas(BigInteger gas) {
		this.gas = gas;
		return this;
	}

	/**
	 * Set the input data for this call.
	 *
	 * @param data
	 * @return
	 */
	public DafnyEvm data(byte[] data) {
		this.callData = data;
		return this;
	}

	/**
	 * Set the code to execute as part of this call.
	 *
	 * @param data
	 * @return
	 */
	public DafnyEvm code(byte[] code) {
		this.code = code;
		return this;
	}

	/**
	 * Set the gas price to use when executing transactions.
	 *
	 * @param gasPrice
	 * @return
	 */
	public DafnyEvm gasPrice(BigInteger gasPrice) {
		this.gasPrice = gasPrice;
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
	 * Get the account associated with a given address. Observe that if the account
	 * doesn't exist, then we create an empty one (which is presumed to be an
	 * end-user account).
	 *
	 * @param address
	 * @return
	 */
	public Account getAccount(BigInteger address) {
		Account acct = worldState.get(address);
		if (acct == null) {
			acct = new Account(null);
			worldState.put(address, acct);
		}
		return acct;
	}

	/**
	 * Create a new account.
	 *
	 * @param address
	 * @return
	 */
	public BigInteger createAccount(BigInteger sender, BigInteger endowment, Optional<BigInteger> salt,
			byte[] initCode) {
		Account acct = worldState.get(sender);
		// Programatically calculate the new address.
		byte[] hash = addr(sender,acct.nonce,salt,initCode);
		// Finally reconstruct the address from the rightmost 160bits.
		BigInteger address = new BigInteger(1, hash);
		// Create the account.
		worldState.put(address, new Account(initCode, endowment, 1));
		return address;
	}

	/**
	 * Perform a call to either an end-user account, or a contract (to be executed
	 * by the Dafny EVM).
	 *
	 * @return
	 */
	public  DafnyEvm.State<?> call() {
		// If code wasn't specified, we assume its coming from the recipient.
		if (this.code == null) {
			this.code = getAccount(recipient).code;
		}
		return call(1);
	}

	/**
	 * Internal call. This expects <code>code</code> to be set, otherwise it treats
	 * it as a call to an <i>end-user account</i>. The reason for this is that it
	 * needs to support different calling conventions, such as those arising from
	 * regular calls, delegate calls, etc.
	 *
	 * @param depth
	 * @return
	 */
	private DafnyEvm.State<?> call(int depth) {
		System.out.println("DEPTH: " + depth + ", " + Hex.toHexString(gas));
		if (depth >= 1024) {
			// The Yellow Paper specifies a maximum depth of 1024.
			return State.from(depth, tracer, new EvmState_Compile.State_INVALID(new Error_CALLDEPTH__EXCEEDED()));
		} else {
			 Account acct = worldState.get(recipient);
			// Determine code to be executed
			byte[] code = this.code;
			//
			if(code == null || code.length == 0) {
				// Must be an End-User Account.
				acct.deposit(value);
				EvmState_Compile.State r = new EvmState_Compile.State_RETURNS(gas, DafnySequence.fromBytes(new byte[0]),
						DafnySequence.empty(Entry._typeDescriptor()));
				tracer.step(depth, r);
				//
				return State.from(depth, tracer,r);
			} else {
				//
				Context_Compile.Raw ctx = Context_Compile.__default.Create(sender, origin, recipient, value, DafnySequence.fromBytes(callData),
						gasPrice, blockInfo.toDafny());
				// Create EVM state
				EvmState_Compile.State st = Create(ctx, new DafnyMap<>(acct.storage), gas, DafnySequence.fromBytes(code));
				// Execute initial code.
				State<?> r = run(depth, tracer, st);
				// Execute the EVM
				while (r instanceof State.Running) {
					if(r instanceof State.CallContinue) {
						r = callContinue((State.CallContinue)r, depth);
					} else {
						r = createContinue((State.CreateContinue)r, depth);
					}
					System.out.println(">>> " + r);

				}
				return r;
			}
		}
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
	private State<?> callContinue(State.CallContinue cc, int depth) {
		// Look up account data
		Account src = getAccount(cc.code());
		// Make the recursive call.
		State<?> nr = new DafnyEvm().tracer(tracer).putAll(worldState).sender(cc.sender()).to(cc.to())
				.code(src.code).origin(origin).value(cc.delegateValue()).data(cc.callData())
				.gasPrice(gasPrice).blockInfo(blockInfo).gas(cc.gas()).call(depth + 1);
		// FIXME: update worldstate upon success.
		// Continue from where we left off.
		return cc.callReturn(nr);
	}

	/**
	 * Manage a nested contract call.
	 *
	 * @param cc    The continuation state.
	 * @param depth The current call depth.
	 * @return
	 */
	private State<?> createContinue(State.CreateContinue cc, int depth) {
		// Determine sender
		BigInteger sender = cc.getEVM().context.address;
		// Construct new account
		BigInteger address = createAccount(sender, cc.endowment(), cc.salt(), cc.initCode());
		// Make the contract call
		State<?> nr = new DafnyEvm().tracer(tracer).putAll(worldState).to(address).sender(sender).code(cc.initCode())
				.origin(origin).gasPrice(gasPrice).blockInfo(blockInfo).call(depth + 1);
		// Check whether execution successful or not.
		if (nr instanceof State.Return) {
			// Create the account!
			Account src = getAccount(address);
			// Configure contract code.
			src.setCode(nr.getReturnData());
		}
		// Continue from where we left off.
		return cc.createReturn(nr, address);
	}

	/**
	 * Execute dafny EVM until it reaches a terminal (or continuation) state.
	 *
	 * @param tracer  Tracer to use for generating debug information (if required).
	 * @param context Enclosing Dafny context.
	 * @param state   Current DafnyEvm state.
	 * @return
	 */
	protected static State<?> run(int depth, Tracer tracer, EvmState_Compile.State state) {
		// Execute it!
		tracer.step(depth,state);
		EvmState_Compile.State r = Execute(state);
		// Continue whilst the EVM is happy.
		while (r instanceof State_OK) {
			tracer.step(depth, r);
			r = Execute(r);
		}
		// Final step
		tracer.step(depth,r);
		// Done
		return State.from(depth, tracer, r);
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
	private byte[] addr(BigInteger sender, BigInteger nonce, Optional<BigInteger> salt, byte[] initCode) {
		byte[] bytes;
		//
		if (salt.isEmpty()) {
			// Case for CREATE
			bytes = RlpEncoder.encode(new RlpList(RlpString.create(sender), RlpString.create(nonce)));
		} else {
			// Case for CREATE2 (see EIP 1014).
			byte ff = (byte) (0xff & 0xff);
			byte[] senderBytes = new Uint160(sender).getBytes();
			byte[] saltBytes = new Uint256(salt.get()).getBytes();
			bytes = concat(new byte[] { ff }, senderBytes, saltBytes, Hash.sha3(initCode));
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
	private byte[] concat(byte[]... arrays) {
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

		public byte[] getReturnData() { return null; }

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
				return new State.Invalid(tracer, (State_INVALID) state, depth);
			} else if (state instanceof State_OK) {
				return new State.Ok(tracer, (State_OK) state, depth);
			} else if (state instanceof State_REVERTS) {
				return new State.Revert(tracer, (State_REVERTS) state, depth);
			} else if (state instanceof State_RETURNS) {
				return new State.Return(tracer, (State_RETURNS) state, depth);
			} else if (state instanceof State_CALLS) {
				return new State.CallContinue(tracer, (State_CALLS) state, depth);
			} else {
				return new State.CreateContinue(tracer, (State_CREATES) state, depth);
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
		public static class Ok extends Running<State_OK> {
			public Ok(Tracer tracer, State_OK state, int depth) {
				super(tracer, state, depth);
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
		public static class CallContinue extends Running<State_CALLS> {
			public CallContinue(Tracer tracer, State_CALLS state, int depth) {
				super(tracer, state, depth);
			}

			/**
			 * Identify the receiver associated with this call.
			 *
			 * @return
			 */
			public BigInteger to() {
				return state.recipient;
			}

			/**
			 * Identify the sender of this call.
			 *
			 * @return
			 */
			public BigInteger sender() {
				return state.sender;
			}

			/**
			 * Identify the contract whose code should be used for executing the call.
			 * Observe that this is not necessarily the same as the receiver (e.g. for the
			 * <code>CALLCODE</code> instruction).
			 *
			 * @return
			 */
			public BigInteger code() {
				return state.code;
			}

			/**
			 * Get the value to be transferred to the recipient by this call.
			 *
			 * @return
			 */
			public BigInteger callValue() {
				return state.callValue;
			}

			/**
			 * Get the call value that should appear in the code as this call is executed.
			 * That will differ from the actual call value if this is a delegate call.
			 *
			 * @return
			 */
			public BigInteger delegateValue() {
				return state.delegateValue;
			}

			/**
			 * Get the gas provided for this call.
			 *
			 * @return
			 */
			public BigInteger gas() {
				return state.gas;
			}

			/**
			 * Get the call data associated with this call.
			 * @return
			 */
			public byte[] callData() {
				return DafnySequence.toByteArray((DafnySequence) state.callData);
			}

			@Override
			protected EvmState_Compile.T getEVM() {
				return state.evm;
			}

			/**
			 * Continue this continuation.
			 *
			 * @return
			 */
			public State<?> callReturn(State<?> callee) {
				// Convert into OK state
				EvmState_Compile.State st = state.CallReturn(callee.state);
				// Continue execution.
				return run(depth, tracer, st);
			}
		}

		/**
		 * Indicates a nested contract creation call (either to a contract or an
		 * end-user account) has been initiated. The intention is that the environment
		 * manages that initialisation for that contract call, and then execution of
		 * this state continues after that is finished (i.e. this is a continuation).
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class CreateContinue extends Running<State_CREATES> {
			public CreateContinue(Tracer tracer, State_CREATES state, int depth) {
				super(tracer, state, depth);
			}

			/**
			 * Get the value to be transferred to created contract.
			 *
			 * @return
			 */
			public BigInteger endowment() {
				return state.endowment;
			}

			/**
			 * Get the (optional) salt associated with this contract creation.
			 *
			 * @return
			 */
			public Optional<BigInteger> salt() {
				ExtraTypes_Compile.Option<BigInteger> salt = state.salt;
				//
				if(salt instanceof ExtraTypes_Compile.Option_Some) {
					ExtraTypes_Compile.Option_Some<BigInteger> s = (ExtraTypes_Compile.Option_Some<BigInteger>) salt;
					return Optional.of(s.v);
				} else {
					return Optional.empty();
				}
			}

			/**
			 * Get the call data associated with this call.
			 * @return
			 */
			public byte[] initCode() {
				return DafnySequence.toByteArray((DafnySequence) state.initcode);
			}

			@Override
			protected EvmState_Compile.T getEVM() {
				return state.evm;
			}

			/**
			 * Continue this continuation.
			 *
			 * @return
			 */
			public State<?> createReturn(State<?> callee, BigInteger address) {
				// Convert into OK state
				EvmState_Compile.State st = state.CreateReturn(callee.state, address);
				// Continue execution.
				return run(depth, tracer, st);
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
			@Override
			public byte[] getReturnData() {
				return DafnySequence.toByteArray(((DafnySequence) state.data));
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
		public static class Return extends State<State_RETURNS> {
			public Return(Tracer tracer, State_RETURNS state, int depth) {
				super(tracer, state, depth);
			}
			/**
			 * Get any return data from this contract call.
			 *
			 * @return
			 */
			@Override
			public byte[] getReturnData() {
				return DafnySequence.toByteArray(((DafnySequence) state.data));
			}

			public BigInteger getGasUsed() {
				// TODO: fixme!
				return BigInteger.ZERO;
			}

			/**
			 * Get the log returned from this running the call.
			 *
			 * @return
			 */
			@Override
			public Pair<BigInteger[], byte[]>[] getLog() {
				DafnySequence<? extends Tuple2> dlog = state.log;
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
				return "RETURN(gas=" + getGasUsed() + "," + Hex.toHexString(getReturnData()) + ")";
			}
		}

		/**
		 * Indicates an exception occurred for some reason (e.g. <i>stack underflow</i>,
		 * <i>out-of-gas</i>, etc.).
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Invalid extends State<State_INVALID> {
			public Invalid(Tracer tracer, State_INVALID state, int depth) {
				super(tracer, state, depth);
			}

			/**
			 * Return the error code associated with this exception.
			 *
			 * @return
			 */
			public EvmState_Compile.Error getErrorCode() {
				return state._a0;
			}

			public BigInteger getGasUsed() {
				// TODO: fixme!
				return BigInteger.ZERO;
			}

			@Override
			public String toString() {
				return "Invalid(" + state._a0.getClass().getSimpleName() + ")";
			}
		}
	}

	/**
	 * Represents all known information associated with a given account. Each
	 * account is either an "end-user account" or a "contract account".
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Account {
		/**
		 * Contract code (or <code>null</code> if this is an end-user account).
		 */
		private byte[] code;
		/**
		 * Current balance of ether.
		 */
		private BigInteger balance;
		/**
		 * Number of transactions this account has made.
		 */
		private BigInteger nonce;
		/**
		 * Current state of the contract storage.
		 */
		private final HashMap<BigInteger,BigInteger> storage;

		public Account(byte[] code) {
			this(code, BigInteger.ZERO, 1);
		}

		public Account(byte[] code, BigInteger balance, long nonce) {
			this(code,balance,nonce,new HashMap<>());
		}

		public Account(byte[] code, BigInteger balance, long nonce, Map<BigInteger,BigInteger> storage) {
			this.code = code;
			this.balance = balance;
			this.storage = new HashMap<>(storage);
			this.nonce = BigInteger.valueOf(nonce);
		}

		public void deposit(BigInteger value) {
			this.balance = this.balance.add(value);
		}

		public BigInteger nonce() {
			return this.nonce;
		}

		public void setCode(byte[] code) {
			this.code = code;
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
		 * Identifies that the EVM has taken a single step of execution (i.e. executed a
		 * bytecode).
		 *
		 * @param evm
		 */
		public void step(int depth, EvmState_Compile.State st);
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
		public final void step(int depth, EvmState_Compile.State st) {
			if (st instanceof State_OK) {
				step(new State.Ok(this, (State_OK) st, depth));
			} else if (st instanceof State_RETURNS) {
				end(new State.Return(this, (State_RETURNS) st, depth));
			} else if (st instanceof State_REVERTS) {
				revert(new State.Revert(this, (State_REVERTS) st, depth));
			} else if (st instanceof State_INVALID) {
				exception(new State.Invalid(this, (State_INVALID) st, depth));
			} else if (st instanceof State_CALLS) {
				callContinue(new State.CallContinue(this, (State_CALLS) st, depth));
			}
		}

		public abstract void step(State.Ok state);

		public abstract void end(State.Return state);

		public abstract void revert(State.Revert state);

		public abstract void exception(State.Invalid state);

		public abstract void callContinue(State.CallContinue state);
	}

}
