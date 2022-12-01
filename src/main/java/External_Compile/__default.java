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
import org.web3j.crypto.ECDSASignature;
import org.web3j.crypto.Hash;
import org.web3j.crypto.Sign;
import org.web3j.crypto.Sign.SignatureData;

import dafny.DafnySequence;
import dafny.Tuple2;
import dafnyevm.util.Bytes;
import dafnyevm.util.Word.Uint160;
import evmtools.util.Hex;
import dafnyevm.crypto.Blake2b;

/**
 * Provides concrete implementations for all methods defined as
 * <code>{:extern}</code> within the DafnyEVM.
 *
 * @author David J. Pearce
 *
 */
public class __default {
    /**
     * Compute the ECDSA key recovery procedure for a given byte sequence.
     *
     * @param h Hash of transaction
     * @param v recovery identifier (assumed to be one byte)
     * @param r
     * @param s
     * @return
     */
    public static DafnySequence<Byte> ECDSARecover(DafnySequence<? extends Byte> _h, byte v, BigInteger r, BigInteger s) {
        byte[] h = DafnySequence.toByteArray((DafnySequence) _h);
//        System.out.println("ECDSARecover(" + Hex.toAbbreviatedHexString(h) + "," + v + "," + r + "," + s + ")");
        ECDSASignature sig = new ECDSASignature(r,s);
        // Recover Key
        try {
            BigInteger key = Sign.recoverFromSignature(v-27, sig, h);
            // Sanity checks
            if(key != null && !key.equals(BigInteger.ZERO)) {
                // Compute KEC
                byte[] hash = Hash.sha3(key.toByteArray());
                // Split out bytes 12--31
                hash = Arrays.copyOfRange(hash, 12, hash.length);
                // Done
                return DafnySequence.fromBytes(leftPad(hash,32));
            }
        } catch(IllegalArgumentException e) {
            // This indicates key recovery was impossible. Therefore, according to the
            // Yellow Paper, we simply return the empty byte sequence.
        }
        //
        return DafnySequence.fromBytes(new byte[0]);
    }

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
		byte[] out = new byte[32];
		digest.doFinal(out, 12);
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
//		System.out.println("MODEXP(" + B + "," + E + "," + M + ")");
		BigInteger r;
		if (M.equals(BigInteger.ZERO)) {
			r = BigInteger.ZERO;
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
     * Compute function F from Blake2 compression algorithm defined in RFC7693. See
     * also EIP-152.
     *
     * @param bytes
     * @return
     */
	public static DafnySequence<Byte> blake2f(DafnySequence<? extends Byte> _bytes) {
	    byte[] bytes = DafnySequence.toByteArray((DafnySequence) _bytes);
	    return DafnySequence.fromBytes(blake2f(bytes));
	}

	public static byte[] blake2f(byte[] bytes) {
        // Initial sanity checks as determined by yellow paper.
        if(bytes.length == 213) {
            // (f)inal block indicator flag
            byte f = bytes[212];
            //
            if(f == 0 || f == 1) {
                // Determine number of rounds.
                long r = Bytes.fromBigEndian32(bytes, 0) & 0xFFFFFFFFL;
                long[] h = Bytes.fromLittleEndian64s(bytes, 4, 8);
                long[] m = Bytes.fromLittleEndian64s(bytes, 68, 16);
                long[] t = Bytes.fromLittleEndian64s(bytes, 196, 2);
                //
                h = Blake2b.F(r, h, m, t, f == 1);
                //
                return Bytes.toLittleEndianBytes(h);
            }
        }
        // Failure case
        return new byte[0];
    }
}
