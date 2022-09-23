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
package External_Compile;

import java.math.BigInteger;

import org.bouncycastle.crypto.digests.RIPEMD160Digest;
import org.web3j.crypto.Hash;

import dafny.DafnySequence;
import dafny.Tuple2;

/**
 * Provides concrete implementations for all methods defined as
 * <code>{:extern}</code> within the DafnyEVM.
 *
 * @author David J. Pearce
 *
 */
public class __default {
	/**
	 * Compute the Keccak256 hash of the byte sequence.
	 *
	 * @param bytes
	 * @return
	 */
	public static BigInteger sha3(DafnySequence<? extends Byte> bytes) {
		// Compute the hash
		byte[] hash = Hash.sha3(bytes.toByteArray((DafnySequence) bytes));
		// Construct an (unsigned) bigint.
		return new BigInteger(1, hash);
	}

	/**
	 * Compute the Sha256 hash of the byte sequence.
	 *
	 * @param bytes
	 * @return
	 */
	public static DafnySequence<Byte> sha256(DafnySequence<? extends Byte> bytes) {
		// Compute the hash
		byte[] hash = Hash.sha256(bytes.toByteArray((DafnySequence) bytes));
		// Construct an (unsigned) bigint.
		return DafnySequence.fromBytes(hash);
	}

	/**
	 * Compute the RIPEMD160 digest.
	 *
	 * @param bytes
	 * @return
	 */
	public static DafnySequence<Byte> ripEmd160(DafnySequence<? extends Byte> _bytes) {
		byte[] bytes = DafnySequence.toByteArray((DafnySequence) _bytes);
		// Compute the hash
		RIPEMD160Digest digest = new RIPEMD160Digest();
		digest.update(bytes, 0, bytes.length);
		byte[] out = new byte[20];
		digest.doFinal(out, 0);
		// Construct an (unsigned) bigint.
		return DafnySequence.fromBytes(out);
	}

	/**
	 * Compute arbitrary precision exponentiation under modulo.  Specifically,
     * we compue B^E % M.  All words are unsigned integers in big endian format.
	 *
	 * @param bytes
	 * @return
	 */
	public static Tuple2<DafnySequence<? extends Byte>, BigInteger> modExp(DafnySequence<? extends Byte> _B,
			DafnySequence<? extends Byte> _E, DafnySequence<? extends Byte> _M) {
		BigInteger B = new BigInteger(1, DafnySequence.toByteArray((DafnySequence) _B));
		byte[] Ebytes = DafnySequence.toByteArray((DafnySequence) _E);
		BigInteger E = new BigInteger(1, Ebytes);
		BigInteger M = new BigInteger(1, DafnySequence.toByteArray((DafnySequence) _M));
		BigInteger r;
		if (B.equals(BigInteger.ZERO) && E.equals(BigInteger.ZERO)) {
			r = BigInteger.ONE.mod(M);
		} else if (E.equals(BigInteger.ZERO)) {
			r = BigInteger.ZERO;
		} else {
			r = B.modPow(E, M);
		}
		BigInteger lEp = lep(E, Ebytes);
		return Tuple2.create(DafnySequence.fromBytes(r.toByteArray()), lEp);
	}

	private static BigInteger lep(BigInteger E, byte[] bytes) {
		boolean zero = E.equals(BigInteger.ZERO);
		//
		if(bytes.length <= 32 && zero) {
			return BigInteger.ZERO;
		} else if(bytes.length <= 32) {
			return BigInteger.valueOf(E.bitLength());
		} else  {
			BigInteger base = BigInteger.valueOf(bytes.length - 32).multiply(BigInteger.valueOf(8));
			long log2 = 0;
			if(bytes[0] != 0) {
				log2 = log2(bytes[0]) + 24;
			} else if(bytes[1] != 0) {
				log2 = log2(bytes[1]) + 16;
			} else if(bytes[2] != 0) {
				log2 = log2(bytes[2]) + 8;
			} else if(bytes[3] != 0) {
				log2 = log2(bytes[3]);
			} else {
				return base;
			}
			return base.add(BigInteger.valueOf(log2));
		}
	}

	private static int log2(byte _b) {
		int b = _b & 0Xff;
		for (int i = 7; i != 0; --i) {
			int mask = 1 << i;
			if ((b & mask) != 0) {
				return i;
			}
		}
		throw new IllegalArgumentException("unreachable code");
	}

	/**
	 * Compute the blake hash of the byte sequence.
	 *
	 * @param bytes
	 * @return
	 */
	public static DafnySequence<Byte> blake2f(DafnySequence<? extends Byte> bytes) {
		// FIXME: this is wrong I believe.
		// Compute the hash
		byte[] hash = Hash.blake2b256(bytes.toByteArray((DafnySequence) bytes));
		// Construct an (unsigned) bigint.
		return DafnySequence.fromBytes(hash);
	}
}
