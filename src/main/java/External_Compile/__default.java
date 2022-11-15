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
import java.util.Arrays;
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
	public static DafnySequence<? extends Byte> modExp(DafnySequence<? extends Byte> _B,
			DafnySequence<? extends Byte> _E, DafnySequence<? extends Byte> _M) {
		BigInteger B = new BigInteger(1, DafnySequence.toByteArray((DafnySequence) _B));
		byte[] Ebytes = DafnySequence.toByteArray((DafnySequence) _E);
		BigInteger E = new BigInteger(1, Ebytes);
		BigInteger M = new BigInteger(1, DafnySequence.toByteArray((DafnySequence) _M));
		//System.out.println("MODEXP(" + B + "," + E + "," + M + ")");
		BigInteger r;
		if (M.equals(BigInteger.ZERO)) {
			r = BigInteger.ZERO;
		} else if (B.equals(BigInteger.ZERO) && E.equals(BigInteger.ZERO)) {
			r = BigInteger.ONE;
		} else {
			r = B.modPow(E, M);
		}
		return DafnySequence.fromBytes(leftPad(r.toByteArray(),_M.length()));
	}

	/**
	 * Pad out a given byte sequence with zeros (to the left) upto a given length.
	 *
	 * @param bytes
	 * @param length
	 * @return
	 */
	private static byte[] leftPad(byte[] bytes, int length) {
	    if(length == bytes.length) {
	        return bytes;
	    } else if(length < bytes.length) {
	        return Arrays.copyOfRange(bytes,0,length);
	    } else {
	        byte[] output = new byte[length];
	        System.arraycopy(bytes, 0, output, output.length - bytes.length, bytes.length);
	        return output;
	    }
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
