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

public class Bytes {

    /**
     * Convert a 64bit word into a sequence of 8 bytes in little endian order.
     *
     * @param w      The word to convert
     * @param offset Offset into the byte array to begin writting bytes.
     * @param bytes  Byte array into which result is placed (must be large enough)
     */
    public static void toLittleEndianBytes(long w, int offset, byte[] bytes) {
        bytes[offset] = (byte) w;
        bytes[offset + 1] = (byte) (w >> 8);
        bytes[offset + 2] = (byte) (w >> 16);
        bytes[offset + 3] = (byte) (w >> 24);
        bytes[offset + 4] = (byte) (w >> 32);
        bytes[offset + 5] = (byte) (w >> 40);
        bytes[offset + 6] = (byte) (w >> 48);
        bytes[offset + 7] = (byte) (w >> 56);
    }

    /**
     * Convert an array of words into an array of bytes, such that each word is
     * stored in little endian order. Thus, the first word is stored at offset
     * <code>0</code> in the resulting array, whilst the second word is at offset
     * <code>8</code>, etc.
     *
     * @param words
     * @return
     */
    public static byte[] toLittleEndianBytes(long[] words) {
        byte[] bytes = new byte[words.length * 8];
        int offset = 0;
        for (int i = 0; i != words.length; ++i) {
            long w = words[i];
            toLittleEndianBytes(w,offset,bytes);
            offset = offset + 8;
        }
        return bytes;
    }

    /**
     * Read a 32-bit word from a byte array stored in big endian representation.
     *
     * @param bytes  Byte array containing bytes to read.
     * @param offset Offset into byte array where bytes are stored.
     * @return
     */
    public static int fromBigEndian32(byte[] bytes, int offset) {
        int b1 = (bytes[offset+3] & 0xff);
        int b2 = (bytes[offset+2] & 0xff) << 8;
        int b3 = (bytes[offset+1] & 0xff) << 16;
        int b4 = (bytes[offset+0] & 0xff) << 24;
        return b1|b2|b3|b4;
    }

    /**
     * Read a 64-bit word from a byte array begining at a given offset.
     *
     * @param bytes  Byte array to read word from.
     * @param offset Offset into array where bytes are stored.
     * @return
     */
    public static long fromLittleEndian64(byte[] bytes, int offset) {
        long b1 = (bytes[offset+0] & 0xffL);
        long b2 = (bytes[offset+1] & 0xffL) << 8;
        long b3 = (bytes[offset+2] & 0xffL) << 16;
        long b4 = (bytes[offset+3] & 0xffL) << 24;
        long b5 = (bytes[offset+4] & 0xffL) << 32;
        long b6 = (bytes[offset+5] & 0xffL) << 40;
        long b7 = (bytes[offset+6] & 0xffL) << 48;
        long b8 = (bytes[offset+7] & 0xffL) << 56;
        return b1|b2|b3|b4|b5|b6|b7|b8;
    }

    /**
     * Convert a sequence of bytes representing <code>n</code> 64bit words store in
     * little endian order. Thus, the first word is stored at offset
     * <code>0</code> in the resulting array, whilst the second word is at offset
     * <code>8</code>, etc.
     *
     * @param bytes  Byte array holding words to be read.
     * @param offset Offset into byte array to begin reading from.
     * @param length Number of words to read.
     * @return
     */
    public static long[] fromLittleEndian64s(byte[] bytes, int offset, int length) {
        long[] words = new long[length];
        for (int i = 0; i != length; ++i) {
            words[i] = fromLittleEndian64(bytes, offset);
            offset += 8;
        }
        return words;
    }

}
