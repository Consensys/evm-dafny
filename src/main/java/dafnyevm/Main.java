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

import static EVM_Compile.__default.*;
import EVM_Compile.Result;
import EVM_Compile.Result_INVALID;
import EVM_Compile.Result_OK;
import EVM_Compile.Result_RETURNS;
import EVM_Compile.Result_REVERT;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import dafny.DafnyMap;
import dafny.DafnySequence;

/**
 * A simple wrapper for the Dafny EVM.
 *
 * @author David J. Pearce
 *
 */
public class Main {
	/**
	 * Print out intermediate states
	 */
	private boolean debug = false;
	/**
	 * Initial state of storage prior.
	 */
	private final DafnyMap<BigInteger,BigInteger> storage;
	/**
	 * EVM Bytecode to execute
	 */
	private final DafnySequence<Byte> code;

	public Main(Map<BigInteger,BigInteger> storage, byte[] code) {
		this.storage = new DafnyMap<>(storage);
		this.code = DafnySequence.fromBytes(code);
	}

	public Main setDebug(boolean debug) {
		this.debug = debug;
		return this;
	}

	public Outcome run() {
		// Create the EVM
		EVM_Compile.T evm = create(storage,BigInteger.ONE,code);
		// Execute it!
		Result r = execute(evm);
		// Continue whilst the EVM is happy.
		while(r instanceof Result_OK) {
			if(debug) {
				System.out.println(toString(evm));
			}
			Result_OK rok = (Result_OK) r;
			evm = rok.evm;
			r = execute(evm);
		}
		// Decide what happened
		if(r instanceof Result_RETURNS) {
			Result_RETURNS rret = (Result_RETURNS) r;
			return new Outcome(false,rret.data,rret.gas,evm);
		} else if(r instanceof Result_REVERT) {
			Result_REVERT rrev = (Result_REVERT) r;
			return new Outcome(true,rrev.data,rrev.gas,evm);
		} else {
			// Sanity check is invalid
			Result_INVALID rinv = (Result_INVALID) r;
			return new Outcome(false,null,null,evm);
		}
	}

	public String toString(EVM_Compile.T evm) {
		final String p = evm.pc.toString();
		final String m = evm.memory.contents.toString();
		final String s = evm.storage.contents.toString();
		final String a = evm.stack.contents.toString();
		return String.format("pc=%s, storage=%s, memory=%s, stack=%s", p, s, m, a);
	}

	/**
	 * A simple class capturing the output of an execution, including the full
	 * machine state.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Outcome {
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

		public Outcome(boolean revert, DafnySequence<? extends Byte> data, BigInteger gas, EVM_Compile.T state) {
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
	}

	public static void main(String[] args) {
		// Parse input string
		byte[] bytes = parseHex(args[0]);
		// Execute the EVM
		Outcome r = new Main(new HashMap<>(),bytes).run();
		//
		System.out.println("REVERT : " + r.isRevert());
		System.out.println("RETDATA: " + r.getReturnData());
		System.out.println("STORAGE: " + r.getStorage());
		System.out.println("MEMORY : " + r.getMemory());
		System.out.println("STACK  : " + r.getStack());
	}

	/**
	 * Parse a string of hex digits (e.g. <code>0F606B</code>) into a byte array.
	 * Note that, the length of the string must be even.
	 *
	 * @param s
	 * @return
	 */
	public static byte[] parseHex(String s) {
		if (s.length() % 2 != 0) {
			throw new IllegalArgumentException("invalid hex string");
		} else {
			final int n = s.length();
			byte[] data = new byte[n >> 1];
			for (int i = 0; i < n; i = i + 2) {
				char ith = s.charAt(i);
				char ithp1 = s.charAt(i+1);
				int val = (Character.digit(ith, 16) << 4) | Character.digit(ithp1, 16);
				data[i / 2] = (byte) val;
			}
			return data;
		}
	}

	/**
	 * Convert a sequence of bytes into a hexadecimal string.
	 *
	 * @param bytes
	 * @return
	 */
	public static String toHexString(byte... bytes) {
		String r = "";
		for(int i=0;i!=bytes.length;++i) {
			int b = bytes[i] & 0xff;
			r = r + String.format("%02X",b);
		}
		return r;
	}
}
