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
package dafnyevm.util;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import dafnyevm.DafnyEvm;
import dafnyevm.DafnyEvm.State;
import dafnyevm.DafnyEvm.Tracer;

/**
 * Encapsulation the notion of an execution context for a given transaction
 * using the Dafny EVM. The context includes, for example, the state of all
 * end-user and contract accounts, the current state of the machine being
 * executed, etc.
 *
 * @author David J. Pearce
 *
 */
public class ExecutionContext {
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
	private static final BigInteger DEFAULT_GAS = new BigInteger("10000000000");
	/**
	 * The mapping from all known contract addresses to their respective account
	 * contents.
	 */
	private final HashMap<BigInteger,Account> state;
	/**
	 * Tracer to use for debugging.
	 */
	private Tracer tracer;

	public ExecutionContext() {
		this.tracer = (ctx, st) -> {
		};
		this.state = new HashMap<>();
	}

	private ExecutionContext(ExecutionContext other) {
		this.state = new HashMap<>(other.state);
		this.tracer = other.tracer;
	}

	public ExecutionContext setTracer(Tracer tracer) {
		this.tracer = tracer;
		return this;
	}

	public Transaction tx() {
		return new Transaction();
	}

	public ExecutionContext put(BigInteger address, Account account) {
		ExecutionContext nthis = new ExecutionContext(this);
		nthis.state.put(address,account);
		return nthis;
	}

	/**
	 * Provides a friendly API for building and executing a transaction.
	 *
	 * @author David J. Pearce
	 *
	 */
	public class Transaction {
		/**
		 * Address of end-user account initiating this call (default is
		 * <code>0xdef</code>).
		 */
		private BigInteger origin = DEFAULT_ORIGIN;
		/**
		 * Address of received for this transaction (default is <code>0xabc</code>).
		 */
		private BigInteger to = DEFAULT_RECEIVER;
		/**
		 * Gas limit for this CALL (default is <code>10000000000</code>)
		 */
		private BigInteger gasLimit = DEFAULT_GAS;
		/**
		 * The value to deposit in this call.
		 */
		private BigInteger value = DEFAULT_VALUE;
		/**
		 * The call data to supply in this call (default is <code>[]</code>).
		 */
		private byte[] calldata = new byte[0];

		/**
		 * Specify from which account this transaction is being initiated.
		 *
		 * @param origin
		 * @return
		 */
		public Transaction from(long origin) {
			this.origin = BigInteger.valueOf(origin);
			return this;
		}

		/**
		 * Specify from which account this transaction is being initiated.
		 *
		 * @param origin
		 * @return
		 */
		public Transaction from(BigInteger origin) {
			this.origin = origin;
			return this;
		}

		/**
		 * Specify some calldata for this transaction.
		 *
		 * @param calldata
		 * @return
		 */
		public Transaction data(byte[] calldata) {
			this.calldata = calldata;
			return this;
		}

		/**
		 * Specify value to deposit as part of this transaction.
		 *
		 * @param value
		 * @return
		 */
		public Transaction value(long value) {
			return value(BigInteger.valueOf(value));
		}

		/**
		 * Specify value to deposit as part of this transaction.
		 *
		 * @param value
		 * @return
		 */
		public Transaction value(BigInteger value) {
			this.value = value;
			return this;
		}

		/**
		 * Run a given sequence of bytecodes, expecting things to go OK and to produce
		 * the given output (i.e. return data).
		 *
		 * @param to Receiver for this call.
		 */
		public DafnyEvm.State call() {
			// FIXME: check sufficient balance for transfer.

			// Extract account info
			Account acct = ExecutionContext.this.state.get(to);
			// FIXME: check for end-user-account.
			return call(acct.storage,acct.code);
		}

		/**
		 * Execute a given sequence of bytecodes using this EVM, assuming an initially
		 * empty storage.
		 *
		 * @param code Code to execute.
		 * @return
		 */
		public DafnyEvm.State call(byte[] code) {
			return call(new HashMap<>(),code);
		}

		/**
		 * Execute a given sequence of bytecodes using this EVM.
		 *
		 * @param storage Initial state of storage.
		 * @param code    Code to execute.
		 * @return
		 */
		public DafnyEvm.State call(Map<BigInteger, BigInteger> storage, byte[] code) {
			return this.call(0,storage,code);
		}

		/**
		 * Helper method for handling a contract call.
		 *
		 * @param storage
		 * @param code
		 * @return
		 */
		private DafnyEvm.State call(int depth, Map<BigInteger, BigInteger> storage, byte[] code) {
			DafnyEvm evm = new DafnyEvm(storage, code).setTracer(tracer);
			// Execute initial code.
			State r = evm.call(to, origin, gasLimit, value, calldata);
			// Execute the EVM
			while (r instanceof State.CallContinue) {
				// Check whether has finished or not.
				State.CallContinue cc = (State.CallContinue) r;
				// A nested contract call has been made.
				Account rx = state.get(cc.receiver());
				// FIXME: write in call data
				State nr = call(depth + 1,rx.storage, rx.code);
				boolean success = nr instanceof State.Return;
				// FIXME: read out return data
				// FIXME: handle reverts, etc.
				// Continue from where we left off.
				r = cc.callContinue(success, nr.getReturnData());
			}
			return r;
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
		private final byte[] code;
		/**
		 * Current balance of ether.
		 */
		private final BigInteger balance;
		/**
		 * Current state of the contract storage.
		 */
		private final HashMap<BigInteger,BigInteger> storage;

		public Account(byte[] code) {
			this(code,BigInteger.ZERO,new HashMap<>());
		}

		public Account(byte[] code, BigInteger balance, Map<BigInteger,BigInteger> storage) {
			this.code = code;
			this.balance = balance;
			this.storage = new HashMap<>(storage);
		}
	}

	// ===================================================================================
	// Helpers
	// ===================================================================================
}
