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
	 * Compute the Sha256 hash of the byte sequence.
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
