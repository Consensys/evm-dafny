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
package dafnyevm.crypto;

public class Blake2b {

    public static long[] F(long r, long[] h, long[] m, long[] t, boolean f) {
        long[] v = new long[16];
        System.arraycopy(h, 0, v, 0, 8);
        System.arraycopy(IV, 0, v, 8, 8);
        v[12] = v[12] ^ t[0];
        v[13] = v[13] ^ t[1];
        //
        if (f) {
            // Invert all bits
            v[14] = ~v[14];
        }
        // Cryptographic mixing
        for (long i = 0; i < r; ++i) {
            int[] s = SIGMA[(int) (i % 10)];
            // NOTE: this differs from RFC7693 but follows the same code provided with
            // EIP-152. Its not clear to me why the EIP deviates from the RFC.
            G1(v,0,4,8,12,m[s[0]]);
            G1(v,1,5,9,13,m[s[1]]);
            G1(v,2,6,10,14,m[s[2]]);
            G1(v,3,7,11,15,m[s[3]]);
            G2(v,1,5,9,13,m[s[5]]);
            G2(v,2,6,10,14,m[s[6]]);
            G2(v,3,7,11,15,m[s[7]]);
            G2(v,0,4,8,12,m[s[4]]);
            G1(v,0,5,10,15,m[s[8]]);
            G1(v,1,6,11,12,m[s[9]]);
            G1(v,2,7,8,13,m[s[10]]);
            G1(v,3,4,9,14,m[s[11]]);
            G2(v,0,5,10,15,m[s[12]]);
            G2(v,1,6,11,12,m[s[13]]);
            G2(v,2,7,8,13,m[s[14]]);
            G2(v,3,4,9,14,m[s[15]]);
        }
        // Xor two halves
        for (int i = 0; i != 8; ++i) {
            h[i] ^= v[i] ^ v[i + 8];
        }
        //
        return h;
    }

    private static void G1(long[] v, int a, int b, int c, int d, long x) {
        v[a] = (v[a] + v[b] + x);
        v[d] = Long.rotateRight(v[d] ^ v[a], 32);
        v[c] = (v[c] + v[d]);
        v[b] = Long.rotateRight(v[b] ^ v[c], 24);
    }

    private static void G2(long[] v, int a, int b, int c, int d, long y) {
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

}
