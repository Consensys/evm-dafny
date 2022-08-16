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
import java.util.HashMap;
import java.util.Map;

import dafnyevm.DafnyEvm;
import dafnyevm.DafnyEvm.Outcome;
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
		this.tracer = new Tracers.Default();
		this.state = new HashMap<>();
	}

	public ExecutionContext setTracer(Tracer tracer) {
		this.tracer = tracer;
		return this;
	}

	public Transaction tx() {
		return new Transaction();
	}

	/**
	 * Provides a friendly API for building and executing a transaction.
	 *
	 * @author David J. Pearce
	 *
	 */
	public class Transaction {
		/**
		 * Gas limit for this CALL (default is <code>10000000000</code>)
		 */
		private BigInteger gasLimit = DEFAULT_GAS;
		/**
		 * The value to deposit in this call.
		 */
		private BigInteger value = BigInteger.ZERO;
		/**
		 * The call data to supply in this call (default is <code>[]</code>).
		 */
		private byte[] calldata = new byte[0];
		/**
		 * Address of end-user account initiating this call (default is <code>1</code>).
		 */
		private BigInteger from = BigInteger.ONE;

		/**
		 * Run a given sequence of bytecodes, expecting things to go OK and to produce
		 * the given output (i.e. return data).
		 *
		 * @param to Receiver for this call.
		 */
		public byte[] call(BigInteger to) {
			// FIXME: check sufficient balance for transfer.

			// Extract account info
			Account acct = ExecutionContext.this.state.get(to);
			System.out.println("Excuting: " + Hex.toHexString(acct.code));
			// FIXME: this is not necessary a contract call!!
			DafnyEvm e = new DafnyEvm(acct.storage, acct.code);
			e.setTracer(tracer);
			// Execute the EVM
			Outcome r = e.call(to, from, gasLimit, value, calldata);
			// Ok!
			return r.getReturnData();
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

		public Account(byte[] code, BigInteger balance, Map<BigInteger,BigInteger> storage) {
			this.code = code;
			this.balance = balance;
			this.storage = new HashMap<>(storage);
		}
	}
}
