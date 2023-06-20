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

import org.bouncycastle.crypto.digests.RIPEMD160Digest;
import org.web3j.crypto.ECDSASignature;
import org.web3j.crypto.Hash;
import org.web3j.crypto.Sign;

import dafny.DafnySequence;
import dafnyevm.crypto.Blake2b;

public class Precompiles {

    // ========================================================================
    // (1) ECDSA Recover
    // ========================================================================


    @SuppressWarnings({"unchecked","rawtypes"})
    public static DafnySequence<Byte> ecdsaRecover(DafnySequence<? extends Byte> _h, byte v, BigInteger r, BigInteger s) {
        byte[] h = DafnySequence.toByteArray((DafnySequence) _h);
        return DafnySequence.fromBytes(ecdsaRecover(h, v, r, s));
    }

    /**
     * Compute the ECDSA key recovery procedure for a given byte sequence.
     *
     * @param h Hash of transaction
     * @param v recovery identifier (assumed to be one byte)
     * @param r
     * @param s
     * @return
     */
    public static byte[] ecdsaRecover(byte[] h, byte v, BigInteger r, BigInteger s) {
        ECDSASignature sig = new ECDSASignature(r, s);
        // Recover Key
        try {
            BigInteger key = Sign.recoverFromSignature(v - 27, sig, h);
            // Sanity checks
            if (key != null && !key.equals(BigInteger.ZERO)) {
                // Compute KEC
                byte[] hash = Hash.sha3(key.toByteArray());
                // Split out bytes 12--31
                hash = Arrays.copyOfRange(hash, 12, hash.length);
                // Done
                return leftPad(hash, 32);
            }
        } catch (IllegalArgumentException e) {
            // This indicates key recovery was impossible. Therefore, according to the
            // Yellow Paper, we simply return the empty byte sequence.
        }
        return new byte[0];
    }

    // ========================================================================
    // (2) SHA256
    // ========================================================================

    @SuppressWarnings({"unchecked","rawtypes"})
    public static DafnySequence<Byte> sha256(DafnySequence<? extends Byte> bytes) {
        byte[] hash = sha256(DafnySequence.toByteArray((DafnySequence) bytes));
        return DafnySequence.fromBytes(hash);
    }

    /**
     * Compute the Sha256 hash of the byte sequence.
     *
     * @param bytes
     * @return
     */
    public static byte[] sha256(byte[] bytes) {
        // Compute the hash
        return Hash.sha256(bytes);
    }

    // ========================================================================
    // (3) RIPEMD160
    // ========================================================================

    @SuppressWarnings({"unchecked","rawtypes"})
    public static DafnySequence<Byte> ripEmd160(DafnySequence<? extends Byte> bytes) {
        byte[] tmp = ripEmd160(DafnySequence.toByteArray((DafnySequence) bytes));
        return DafnySequence.fromBytes(tmp);
    }

    /**
     * Compute the RIPEMD160 digest.
     *
     * @param bytes
     * @return
     */
    public static byte[] ripEmd160(byte[] bytes) {
        // Compute the hash
        RIPEMD160Digest digest = new RIPEMD160Digest();
        digest.update(bytes, 0, bytes.length);
        byte[] out = new byte[32];
        digest.doFinal(out, 12);
        // Construct an (unsigned) bigint.
        return out;
    }

    // ========================================================================
    // (9) BLAKE2f
    // ========================================================================

    public static DafnySequence<Byte> blake2f(DafnySequence<? extends Byte> _bytes) {
        @SuppressWarnings({"unchecked","rawtypes"})
        byte[] bytes = DafnySequence.toByteArray((DafnySequence) _bytes);
        return DafnySequence.fromBytes(blake2f(bytes));
    }

    /**
     * Compute function F from Blake2 compression algorithm defined in RFC7693. See
     * also EIP-152.
     *
     * @param bytes
     * @return
     */
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

    // ========================================================================
    // KECCAK256
    // ========================================================================

    @SuppressWarnings({"unchecked","rawtypes"})
    public static BigInteger sha3(DafnySequence<? extends Byte> bytes) {
        return sha3(DafnySequence.toByteArray((DafnySequence) bytes));
    }

    /**
     * Compute the Keccak256 hash of the byte sequence.
     *
     * @param bytes
     * @return
     */
    public static BigInteger sha3(byte[] bytes) {
        // Compute the hash
        byte[] hash = Hash.sha3(bytes);
        // Construct an (unsigned) bigint.
        return new BigInteger(1, hash);
    }

    // ========================================================================
    // Helpers
    // ========================================================================

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
}
