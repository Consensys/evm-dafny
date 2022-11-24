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
import dafnyevm.util.Word.Uint160;
import evmtools.util.Hex;

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
	    // Initial sanity checks as determined by yellow paper.
	    if(_bytes.length() == 213) {
	        byte[] bytes = DafnySequence.toByteArray((DafnySequence) _bytes);
	        // (f)inal block indicator flag
	        byte f = bytes[212];
	        //
	        if(f == 0 || f == 1) {
	            // Determine number of rounds.
                long r = fromBigEndian32(bytes, 0);
                long[] h = fromLittleEndian64s(bytes, 4, 8);
                long[] m = fromLittleEndian64s(bytes, 68, 16);
                long[] t = fromLittleEndian64s(bytes, 196, 2);
                //
                h = F(r, h, m, t, f == 1);
                //
                System.out.println("HASH: " + Hex.toHexString(toLittleEndianBytes(h)));
                //
                return DafnySequence.fromBytes(toLittleEndianBytes(h));
	        }
	    }
	    // Failure case
	    return DafnySequence.fromBytes(new byte[0]);
	}

	private static long[] F(long r, long[] h, long[] m, long[] t, boolean f) {
	    long[] v = new long[16];
	    System.arraycopy(h, 0, v, 0, 8);
        System.arraycopy(IV, 0, v, 8, 8);
	    v[12] = v[12] ^ t[0];
	    v[13] = v[13] ^ t[1];
	    //
	    if(f) {
	        // Invert all bits
            v[14] = ~v[14];
	    }
	    // Cryptographic mixing
	    System.out.println("R=" + r);
        for (long i = 0; i < r; ++i) {
	        int[] s = SIGMA[(int) (i%10)];
            G(v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
            G(v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
            G(v, 2, 6, 10, 14, m[s[4]], m[s[5]] );
            G(v, 3, 7, 11, 15, m[s[6]], m[s[7]] );
            G(v, 0, 5, 10, 15, m[s[8]], m[s[9]] );
            G(v, 1, 6, 11, 12, m[s[10]], m[s[11]] );
            G(v, 2, 7,  8, 13, m[s[12]], m[s[13]] );
            G(v, 3, 4,  9, 14, m[s[14]], m[s[15]] );
	    }
	    // Xor two halves
        for (int i = 0; i != 8; ++i) {
            h[i] ^= v[i] ^ v[i + 8];
        }
	    //
	    return h;
	}

    // Blake2 Mixing Function
    private static void G(long[] v, int a, int b, int c, int d, long x, long y) {
        v[a] = (v[a] + v[b] + x);
        v[d] = Long.rotateRight(v[d] ^ v[a], 32);
        v[c] = (v[c] + v[d]);
        v[b] = Long.rotateRight(v[b] ^ v[c], 24);
        v[a] = (v[a] + v[b] + y);
        v[d] = Long.rotateRight(v[d] ^ v[a], 16);
        v[c] = (v[c] + v[d]);
        v[b] = Long.rotateRight(v[b] ^ v[c], 63);
    }

    // Blake2b Initialisation Vector
	private static final long[] IV = {
	        0x6A09E667F3BCC908L, 0xBB67AE8584CAA73BL,
	        0x3C6EF372FE94F82BL, 0xA54FF53A5F1D36F1L,
	        0x510E527FADE682D1L, 0x9B05688C2B3E6C1FL,
	        0x1F83D9ABFB41BD6BL, 0x5BE0CD19137E2179L
	};

	private static final int[][] SIGMA = new int[][]{
//	    {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15},
//	    {14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3},
//	    {11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4},
//	    {7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8},
//	    {9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13},
//	    {2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9},
//	    {12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11},
//	    {13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10},
//	    {6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5},
//	    {10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0}
	    {0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15},
	    {14,4,9,13,10,8,15,6,1,0,11,5,12,2,7,3},
	    {11,12,5,15,8,0,2,13,10,3,7,9,14,6,1,4},
	    {7,3,13,11,9,1,12,14,2,5,4,15,6,10,0,8},
	    {9,5,2,10,0,7,4,15,14,11,6,3,1,12,8,13},
	    {2,6,0,8,12,10,11,3,4,7,15,1,13,5,14,9},
	    {12,1,14,4,5,15,13,10,0,6,9,8,7,3,2,11},
	    {13,7,12,3,11,14,1,9,5,15,8,2,0,4,6,10},
	    {6,14,11,0,15,9,3,8,12,13,1,10,2,7,4,5},
	    {10,8,7,1,2,4,6,5,15,9,3,13,11,14,12,0},
	};

    private static long[] fromLittleEndian64s(byte[] bytes, int offset, int length) {
        long[] words = new long[length];
        for (int i = 0; i != length; ++i) {
            words[i] = fromLittleEndian64(bytes, offset);
            offset += 8;
        }
        return words;
    }

	private static long fromLittleEndian64(byte[] bytes, int offset) {
	    byte b1 = bytes[offset];
	    byte b2 = bytes[offset+1];
	    byte b3 = bytes[offset+2];
	    byte b4 = bytes[offset+3];
	    byte b5 = bytes[offset+4];
	    byte b6 = bytes[offset+5];
	    byte b7 = bytes[offset+6];
	    byte b8 = bytes[offset+7];
	    long w = (b1 & 0xff);
	    w |= (b2 & 0xff) << 8;
	    w |= (b3 & 0xff) << 16;
	    w |= (b4 & 0xff) << 24;
	    w |= (b5 & 0xff) << 32;
	    w |= (b6 & 0xff) << 40;
	    w |= (b7 & 0xff) << 48;
	    w |= (b8 & 0xff) << 56;
	    return w;
	}

	private static long fromBigEndian32(byte[] bytes, int offset) {
        byte b1 = bytes[offset];
        byte b2 = bytes[offset+1];
        byte b3 = bytes[offset+2];
        byte b4 = bytes[offset+3];
        long w = (b4 & 0xff);
        w |= (b3 & 0xff) << 8;
        w |= (b2 & 0xff) << 16;
        w |= (b1 & 0xff) << 24;
        return w;
    }

	/**
     * Convert an array of words into an array of bytes, such that each word is
     * stored in little endian order.
     *
     * @param words
     * @return
     */
	private static byte[] toLittleEndianBytes(long[] words) {
	    byte[] bytes = new byte[words.length * 8];
	    int offset = 0;
        for (int i = 0; i != words.length; ++i) {
            long w = words[i];
            bytes[offset] = (byte) (w & 0xff);
            bytes[offset + 1] = (byte) ((w >> 8) & 0xff);
            bytes[offset + 2] = (byte) ((w >> 16) & 0xff);
            bytes[offset + 3] = (byte) ((w >> 24) & 0xff);
            bytes[offset + 4] = (byte) ((w >> 32) & 0xff);
            bytes[offset + 5] = (byte) ((w >> 40) & 0xff);
            bytes[offset + 6] = (byte) ((w >> 48) & 0xff);
            bytes[offset + 7] = (byte) ((w >> 56) & 0xff);
            offset = offset + 8;
        }
	    return bytes;
	}
}
