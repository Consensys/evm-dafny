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

import EvmState_Compile.State_CALLS;
import EvmState_Compile.State_CREATES;
import EvmState_Compile.State_INVALID;
import EvmState_Compile.State_OK;
import EvmState_Compile.State_RETURNS;
import EvmState_Compile.State_REVERTS;
import WorldState_Compile.Account;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafny.Tuple2;
import evmtools.util.Hex;
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
	 * Default balance for origin of a call (unless otherwise specified).
	 */
	public final static BigInteger DEFAULT_BALANCE = BigInteger.valueOf(10000);
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
	private DafnyMap<BigInteger, Account> worldState = new DafnyMap<>();
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
		Storage_Compile.T store = Storage_Compile.T.create(new DafnyMap<BigInteger,BigInteger>(storage));
		Code_Compile.Raw code = new Code_Compile.Raw(DafnySequence.fromBytes(bytecode));
		WorldState_Compile.Account acct = WorldState_Compile.__default.CreateAccount(nonce, endowment, store,code);
		this.worldState = DafnyMap.update(worldState, address, acct);
		return this;
	}

	/**
	 * Perform a call to either an end-user account, or a contract (to be executed
	 * by the Dafny EVM).
	 *
	 * @return
	 */
	public  DafnyEvm.State<?> call() {
		// Sanity check whether sender's account exists!
		if(!worldState.contains(sender)) {
			// If not, create it.
			create(sender,DEFAULT_BALANCE);
		}
		Account c = worldState.get(recipient);
		@SuppressWarnings({ "unchecked", "rawtypes" })
		byte[] code = DafnySequence.toByteArray((DafnySequence) c.dtor_code().dtor_contents());
		// Construct the transaction context for the call.
		Context_Compile.Raw ctx = Context_Compile.__default.Create(sender, origin, recipient, value,
				DafnySequence.fromBytes(callData), gasPrice, blockInfo.toDafny());
		// Construct world state
		WorldState_Compile.T ws = WorldState_Compile.T.create(worldState, new DafnySet<>());
		// Construct initial substate
		SubState_Compile.T ss = SubState_Compile.__default.Create();
		// Mark sender + recipient as having been accessed.
		ss = ss.AccountAccessed(sender);
		ss = ss.AccountAccessed(recipient);
		// Construct bytecode to execute
		DafnySequence<Byte> bytecode = DafnySequence.fromBytes(code);
		// Begin the call.
		EvmState_Compile.State st = EvmState_Compile.__default.Call(ws, ctx, ss, bytecode, value, gas, BigInteger.ONE);
		// Execute bytecodes!
		st = run(1, tracer, st);
		// Convert back into the Java API
		return State.from(1,tracer,st);
	}

	/**
	 * Perform a contract creation.
	 *
	 * @return
	 */
	public DafnyEvm.State<?> create() {
		@SuppressWarnings({ "unchecked", "rawtypes" })
		DafnySequence<Byte> code = DafnySequence.fromBytes(callData);
		// Determine sender's nonce
		BigInteger nonce = worldState.get(sender).dtor_nonce();
		// NOTE: we do not subtract one from the nonce here, as this address is being
		// calculated *before* the sender's nonce is incremented.
		BigInteger address = addr(sender,nonce);
		// Construct the transaction context for the call.
		Context_Compile.Raw ctx = Context_Compile.__default.Create(sender, origin, address, value,
				code, gasPrice, blockInfo.toDafny());
		// Construct world state
		WorldState_Compile.T ws = WorldState_Compile.T.create(worldState, new DafnySet<>());
		// Construct initial substate
		SubState_Compile.T ss = SubState_Compile.__default.Create();
		// Begin the call.
		EvmState_Compile.State st = EvmState_Compile.__default.Create(ws, ctx, ss, code, gas, BigInteger.ONE);
		// Execute bytecodes!
		st = run(1, tracer, st);
		// Convert back into the Java API
		return State.from(1,tracer,st);
	}

	/**
	 * Execute dafny EVM until it reaches a terminal (or continuation) state.
	 *
	 * @param tracer  Tracer to use for generating debug information (if required).
	 * @param context Enclosing Dafny context.
	 * @param state   Current DafnyEvm state.
	 * @return
	 */
	protected static EvmState_Compile.State run(int depth, Tracer tracer, EvmState_Compile.State st) {
		// Continue whilst the EVM is happy.
		while (st instanceof State_OK) {
			tracer.step(depth, st);
			st = Execute(st);
			// Manage continuations
			if (st instanceof State_CALLS) {
				st = callContinue(depth, tracer, (State_CALLS) st);
			} else if(st instanceof State_CREATES){
				st = createContinue(depth, tracer, (State_CREATES) st);
			}
		}
		// Final step
		tracer.step(depth, st);
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
	private static EvmState_Compile.State callContinue(int depth, Tracer tracer, EvmState_Compile.State_CALLS cc) {
		EvmState_Compile.Raw evm = cc.dtor_evm();
		// Identify account whose code to execute
		Account c = evm.dtor_world().dtor_accounts().get(cc.dtor_code());
		DafnySequence<? extends Byte> code = (c != null) ? c.dtor_code().dtor_contents() : DafnySequence.fromBytes(new byte[0]);
		// Begin recursive call.
		EvmState_Compile.State st = cc.CallEnter(BigInteger.valueOf(depth), code);
		// Run code within recursive call.
		st = run(depth + 1, tracer, st);
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
	private static EvmState_Compile.State createContinue(int depth, Tracer tracer, EvmState_Compile.State_CREATES cc) {
		// Determine sender
		BigInteger sender = cc.dtor_evm().dtor_context().dtor_address();
		// Construct new account
		Account acct = cc.dtor_evm().dtor_world().dtor_accounts().get(sender);
		// NOTE: we do not subtract one from the nonce here, as this address is being
		// calculated *before* the sender's nonce is incremented.
		byte[] hash = addr(sender, acct.dtor_nonce(), cc.dtor_salt(), cc.dtor_initcode());
		// Finally reconstruct the address from the rightmost 160bits.
		BigInteger address = new BigInteger(1, hash);
		// Begin the recursive call.
		EvmState_Compile.State st = cc.CreateEnter(BigInteger.valueOf(depth), address, cc.dtor_initcode());
		// Run init code for recursive call.
		st = run(depth + 1, tracer, st);
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
		byte[] hash = addr(sender,nonce,new ExtraTypes_Compile.Option_None<>(),null);
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
	public static byte[] addr(BigInteger sender, BigInteger nonce, ExtraTypes_Compile.Option<BigInteger> salt,
			DafnySequence<? extends Byte> initCode) {
		byte[] bytes;
		//
		if (salt instanceof ExtraTypes_Compile.Option_None) {
			// Case for CREATE
			bytes = RlpEncoder.encode(new RlpList(RlpString.create(sender),RlpString.create(nonce)));
		} else {
			@SuppressWarnings({ "rawtypes", "unchecked" })
			byte[] code = DafnySequence.toByteArray((DafnySequence) initCode);
			ExtraTypes_Compile.Option_Some<BigInteger> s = (ExtraTypes_Compile.Option_Some<BigInteger>) salt;
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
			public BigInteger getRemainingGas() {
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
				DafnySequence bytes = getEVM().dtor_memory().dtor_contents();
				return DafnySequence.toByteArray(bytes);
			}

			/**
			 * Get the current size of memory (in bytes).
			 *
			 * @return
			 */
			public int getMemorySize() {
				return getEVM().dtor_memory().dtor_contents().length();
			}

			/**
			 * Get the state of the stack when the machine halted.
			 *
			 * @return
			 */
			public BigInteger[] getStack() {
				DafnySequence<? extends BigInteger> dStack = getEVM().dtor_stack().dtor_contents();
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
				DafnyMap<? extends BigInteger, ? extends BigInteger> m = a.dtor_storage().dtor_contents();
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
		public static class Ok extends Running<State_OK> {
			public Ok(Tracer tracer, State_OK state, int depth) {
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

			public BigInteger getGasRefunded() {
				return state.dtor_gas();
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

			public BigInteger getGasRefunded() {
				return state.dtor_gas();
			}

			public Map<BigInteger,evmtools.core.Account> getWorldState() {
				return toWorldState(state.dtor_world());
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
				return "RETURN(gas=" + getGasRefunded() + "," + Hex.toHexString(getReturnData()) + "," + ws + ")";
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

		private static Map<BigInteger, evmtools.core.Account> toWorldState(WorldState_Compile.T world) {
			DafnyMap<? extends BigInteger, ? extends Account> accounts = world.dtor_accounts();
			HashMap<BigInteger, evmtools.core.Account> ws = new HashMap<>();
			for (BigInteger account : accounts.keySet().Elements()) {
				Account a = accounts.get(account);
				@SuppressWarnings({ "rawtypes", "unchecked" })
				byte[] bytecode = DafnySequence.toByteArray((DafnySequence) a.dtor_code().dtor_contents());
				Map<BigInteger, BigInteger> store = new HashMap<>();
				DafnyMap<? extends BigInteger, ? extends BigInteger> m = a.dtor_storage().dtor_contents();
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
			} else  {
				throw new IllegalArgumentException("invalid state encountered (" + st.getClass().getName() + ")");
			}
		}

		public abstract void step(State.Ok state);

		public abstract void end(State.Return state);

		public abstract void revert(State.Revert state);

		public abstract void exception(State.Invalid state);
	}

}
