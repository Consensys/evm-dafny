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

import org.web3j.crypto.Hash;
import java.math.BigInteger;

public abstract class Word {
	private final byte[] bytes;

	protected Word(int n) {
		this.bytes = new byte[n];
	}

	protected Word(int n, long v) {
		if (n < 8) {
			throw new IllegalArgumentException("invalid byte array (too short)");
		}
		this.bytes = new byte[n];
		this.bytes[n-8] = (byte) ((v >> 56) & 0xff);
		this.bytes[n-7] = (byte) ((v >> 48) & 0xff);
		this.bytes[n-6] = (byte) ((v >> 40) & 0xff);
		this.bytes[n-5] = (byte) ((v >> 32) & 0xff);
		this.bytes[n-4] = (byte) ((v >> 24) & 0xff);
		this.bytes[n-3] = (byte) ((v >> 16) & 0xff);
		this.bytes[n-2] = (byte) ((v >> 8) & 0xff);
		this.bytes[n-1] = (byte) (v & 0xff);
	}

	protected Word(int n, byte[] bytes) {
		if (bytes.length > n) {
			throw new IllegalArgumentException("invalid byte array (too big)");
		}
		this.bytes = new byte[n];
		int padding = n - bytes.length;
		System.arraycopy(bytes, 0, this.bytes, padding, bytes.length);
	}

	/**
	 * Access the bytes making up this word. Observe that bytes are always stored in
	 * _big endian_ order.
	 *
	 * @return
	 */
	public byte[] getBytes() {
		return bytes;
	}

	/**
	 * Get the SHA3 hash of this word.
	 *
	 * @return
	 */
	public byte[] sha3() {
		return Hash.sha3(this.bytes);
	}

	/**
	 * Represents a 160 bit unsigned integer.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Uint64 extends Word {
		public static final Uint64 ZERO = new Uint64();

		public Uint64() {
			super(8);
		}

		public Uint64(long v) {
			super(8, v);
		}

		public Uint64(BigInteger v) {
			super(8, v.toByteArray());
		}
	}

	/**
	 * Represents a 160 bit unsigned integer.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Uint160 extends Word {
		public static final Uint160 ZERO = new Uint160();

		public Uint160() {
			super(20);
		}

		public Uint160(long v) {
			super(20, v);
		}

		public Uint160(BigInteger v) {
			super(20, v.toByteArray());
		}
	}

	/**
	 * Represents a 256 bit unsigned integer.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Uint256 extends Word {
		public static final Uint256 ZERO = new Uint256();

		public Uint256() {
			super(32);
		}

		public Uint256(long v) {
			super(32, v);
		}

		public Uint256(BigInteger v) {
			super(32, v.toByteArray());
		}
	}
}
