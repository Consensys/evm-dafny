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

public class Hex {

	/**
	 * Decode a hexidecimal string (possibly starting with "0x") into a BigInteger.
	 *
	 * @param hex
	 * @return
	 */
	public static BigInteger toBigInt(String hex) {
		// Skip "0x" if string starts with it.
		if (hex.startsWith("0x")) { hex = hex.substring(2); }
		return new BigInteger(hex, 16);
	}

	/**
	 * Parse a string of hex digits (e.g. <code>0F606B</code>) into a byte array.
	 * Note that, the length of the string must be even.
	 *
	 * @param s
	 * @return
	 */
	public static byte[] toBytes(String s) {
		if (s.length() % 2 != 0) {
			throw new IllegalArgumentException("invalid hex string");
		} else {
			// Skip "0x" if string starts with it.
			if(s.startsWith("0x")) {
				s = s.substring(2);
			}
			// Parse the string.
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
			r = r + String.format("%02x",b);
		}
		return "0x" + r;
	}

	/**
	 * Convert a biginteger into a hexadecimal string.
	 *
	 * @param bytes
	 * @return
	 */
	public static String toHexString(BigInteger i) {
		return "0x" + i.toString(16);
	}
}
