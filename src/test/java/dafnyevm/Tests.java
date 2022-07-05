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
package dafnyevm;
import java.util.HashMap;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import dafny.DafnySequence;
import dafnyevm.Main.Outcome;
import static dafnyevm.Main.parseHex;
import static dafnyevm.util.Bytecodes.*;


public class Tests {
	/**
	 * Enable to see additional debug information (e.g. internal states).
	 */
	private final boolean DEBUG = true;

	// ========================================================================
	// STOP
	// ========================================================================

	@Test
	public void test_stop_01() {
		runExpecting(new int[] { STOP });
	}

	// ========================================================================
	// PUSH, RETURN, POP
	// ========================================================================

	@Test
	public void test_push1_01() {
		runExpecting(new int[] { PUSH1, 0x00, PUSH1, 0x00, RETURN });
	}

	@Test
	public void test_push1_02() {
		runExpecting(new int[] { PUSH1, 0x01, PUSH1, 0x00, RETURN }, new byte[] { 0 });
	}

	@Test
	public void test_push2_01() {
		runExpecting(new int[] { PUSH2, 0x00, 0x02, PUSH1, 0x00, RETURN }, new byte[] { 0, 0 });
	}

	@Test
	public void test_pop_01() {
		runExpecting(new int[] { PUSH1, 0x02, PUSH1, 0x01, POP, PUSH1, 0x00, RETURN }, new byte[] { 0, 0 });
	}

	// ========================================================================
	// MLOAD, MSTORE
	// ========================================================================

	@Test
	public void test_mstore_01() {
		// Check words stored in big endian format.
		runExpecting(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x1, PUSH1, 0x00, RETURN }, new byte[] { 0 });
	}

	@Test
	public void test_mstore_02() {
		// Check can return data from memory.
		runExpecting(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x7b));
	}

	@Test
	public void test_mstore_03() {
		// Check can return data from memory.
		runExpecting(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x4d7b));
	}

	@Test
	public void test_mload_01() {
		// Check can read and write data to memory
		runExpecting(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x00, MLOAD, PUSH1, 0x20, MSTORE, PUSH1, 0x20, PUSH1, 0x20, RETURN }, UINT256(0x4d7b));
	}

	// ========================================================================
	// MSTORE8
	// ========================================================================

	@Test
	public void test_mstore8_01() {
		// Check words stored in big endian format.
		runExpecting(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE8, PUSH1, 0x1, PUSH1, 0x00, RETURN }, new byte[] { 0x7b });
	}

	@Test
	public void test_mstore8_02() {
		// Check can return data from memory.
		runExpecting(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE8, PUSH1, 0x20, PUSH1, 0x00, RETURN },
				shl(UINT256(0x7b), 31));
	}

	@Test
	public void test_mstore8_03() {
		// Check can return data from memory.
		runExpecting(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, MSTORE8, PUSH1, 0x20, PUSH1, 0x00, RETURN },
				shl(UINT256(0x7b), 31));
	}

	// ========================================================================
	// ADD / SUB / DIV / MUL
	// ========================================================================

	@Test
	public void test_add_01() {
		// 2 + 1 => 3
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x2, ADD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x3));
	}

	@Test
	public void test_sub_01() {
		// 3 - 1 => 2
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x3, SUB, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x2));
	}

	@Test
	public void test_sub_02() {
		// 0 - 6 => -6
		runExpecting(new int[] { PUSH1, 0x6, PUSH1, 0x0, SUB, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, not(UINT256(0x5)));
	}

	@Test
	public void test_mul_01() {
		// 2 * 3 => 6
		runExpecting(new int[] { PUSH1, 0x3, PUSH1, 0x2, MUL, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x6));
	}

	@Test
	public void test_div_01() {
		// 6 / 2 => 3
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x6, DIV, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x3));
	}

	@Test
	public void test_sdiv_01() {
		// 6 / 2 => 3
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x6, SDIV, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x3));
	}

	@Test
	public void test_sdiv_02() {
		// -6 / 2 => -3
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x6, PUSH1, 0x0, SUB, SDIV, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, not(UINT256(0x2)));
	}

	@Test
	public void test_sdiv_03() {
		// -6 / -2 => 3
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x6, PUSH1, 0x0, SUB, SDIV, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x3));
	}

	// ========================================================================
	// AND / OR / XOR / NOT
	// ========================================================================

	@Test
	public void test_and_01() {
		// 0b0001 & 0b0001  => 0b0001
		runExpecting(new int[] { PUSH1, 0b0001, PUSH1, 0b0001, AND, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b0001));
	}

	@Test
	public void test_and_02() {
		// 0b0001 & 0b0011  => 0b0001
		runExpecting(new int[] { PUSH1, 0b0011, PUSH1, 0b0001, AND, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b0001));
	}

	@Test
	public void test_and_03() {
		// 0b0101 & 0b0011  => 0b0001
		runExpecting(new int[] { PUSH1, 0b0011, PUSH1, 0b0101, AND, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b0001));
	}

	@Test
	public void test_or_01() {
		// 0b0001 | 0b0001  => 0b0001
		runExpecting(new int[] { PUSH1, 0b0001, PUSH1, 0b0001, OR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b0001));
	}

	@Test
	public void test_or_02() {
		// 0b0001 | 0b0011  => 0b0011
		runExpecting(new int[] { PUSH1, 0b0011, PUSH1, 0b0001, OR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b0011));
	}

	@Test
	public void test_or_03() {
		// 0b0101 | 0b0011  => 0b0111
		runExpecting(new int[] { PUSH1, 0b0011, PUSH1, 0b0101, OR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b0111));
	}

	@Test
	public void test_xor_01() {
		// 0b0001 ^ 0b0001  => 0b0000
		runExpecting(new int[] { PUSH1, 0b0001, PUSH1, 0b0001, XOR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b0000));
	}

	@Test
	public void test_xor_02() {
		// 0b0001 ^ 0b0011  => 0b0010
		runExpecting(new int[] { PUSH1, 0b0011, PUSH1, 0b0001, XOR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b0010));
	}

	@Test
	public void test_xor_03() {
		// 0b0101 ^ 0b0011  => 0b0110
		runExpecting(new int[] { PUSH1, 0b0011, PUSH1, 0b0101, XOR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b0110));
	}

	@Test
	public void test_not_01() {
		// ~0b00000101 => 0b11111010
		runExpecting(new int[] { PUSH1, 0b0101, NOT, PUSH1, 0x1F, MSTORE8, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0b11111010));
	}

	@Test
	public void test_not_02() {
		// ~0b00000101 => 0b11111010
		runExpecting(new int[] { PUSH1, 0b0101, NOT, PUSH1, 0x0, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, not(UINT256(0b00000101)));
	}

	// ========================================================================
	// LT / GT / SLT / SGT / EQ / ISZERO
	// ========================================================================

	@Test
	public void test_lt_01() {
		// 2 < 1 = 0
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x2, LT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_lt_02() {
		// 1 < 2 = 1
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x1, LT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x1));
	}

	@Test
	public void test_lt_03() {
		// 2 < 2 => 0
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x2, LT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_gt_01() {
		// 2 > 1 => 1
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x2, GT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x1));
	}

	@Test
	public void test_gt_02() {
		// 1 > 2 => 0
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x1, GT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_gt_03() {
		// 2 > 2 => 0
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x2, GT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_slt_01() {
		// -2 < 1 => 1
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x2, PUSH1, 0x0, SUB, SLT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x1));
	}

	@Test
	public void test_slt_02() {
		// 1 < -2 => 0
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x1, SLT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_slt_03() {
		// -2 < -1 => 1
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x0, SUB, PUSH1, 0x2, PUSH1, 0x0, SUB, SLT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x1));
	}

	@Test
	public void test_slt_04() {
		// -1 < -2 => 0
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x1, PUSH1, 0x0, SUB, SLT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_sgt_01() {
		// -2 > 1 => 0
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x2, PUSH1, 0x0, SUB, SGT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_sgt_02() {
		// 1 > -2 => 1
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x1, SGT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x1));
	}

	@Test
	public void test_sgt_03() {
		// -2 > -1 => 0
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x0, SUB, PUSH1, 0x2, PUSH1, 0x0, SUB, SGT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_sgt_04() {
		// -1 > -2 => 1
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x1, PUSH1, 0x0, SUB, SGT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x1));
	}

	@Test
	public void test_eq_01() {
		// 2 = 1 => 0
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x2, EQ, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_eq_02() {
		// 2 = 2 => 1
		runExpecting(new int[] { PUSH1, 0x2, PUSH1, 0x2, EQ, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x1));
	}

	@Test
	public void test_iszero_01() {
		// 2 = 0 => 0
		runExpecting(new int[] { PUSH1, 0x2, ISZERO, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x0));
	}

	@Test
	public void test_iszero_02() {
		// 0 = 0 => 1
		runExpecting(new int[] { PUSH1, 0x0, ISZERO, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x1));
	}

	// ========================================================================
	// SLOAD, SSTORE
	// ========================================================================

	@Test
	public void test_sstore_01() {
		// test add11 from the reference tests
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x1, ADD, PUSH1, 0x00, SSTORE, STOP }, new byte[0]);
		//runExpecting("600160010160005500", new byte[0]);
	}

	@Test
	public void test_sstore_02() {
		runExpecting(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, SSTORE, PUSH1, 0x00, SLOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT256(0x4d7b));
	}

	// ========================================================================
	// Misc
	// ========================================================================

	@Test
	public void test_highmemory_write_01() {
		// Check out-of-gas for high memory write.
		runOutOfGas(new int[] {
				PUSH1, 0x7b,
				PUSH32,
				0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 08 bytes
				0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 16 bytes
				0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 24 bytes
				0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 32 bytes
				MSTORE, STOP });
	}

	@Test
	public void test_highmemory_write_02() {
		// Check out-of-gas for high memory write.
		runOutOfGas(new int[] {
				PUSH1, 0x7b,
				PUSH32,
				0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 08 bytes
				0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 16 bytes
				0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 24 bytes
				0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xE0, // 32 bytes
				MSTORE, STOP });
	}

	/**
	 * Run a given sequence of bytecodes, expecting things to go OK and to produce
	 * the given output.
	 *
	 * @param bytecode
	 * @param bytes
	 */
	private void runExpecting(byte[] code, byte... bytes) {
		System.out.println("Excuting: " + Main.toHexString(code));
		// Execute the EVM
		Outcome r = new Main(new HashMap<>(),code).setDebug(DEBUG).run();
		// Check we haven't reverted
		assertFalse(r.isRevert());
		// Check something was returned
		assertTrue(r.getReturnData() != null);
		// Ok!
		assertEquals(DafnySequence.fromBytes(bytes), r.getReturnData());
	}

	/**
	 * Overload of <code>runExpecting</code> where input specified as text.
	 *
	 * @param hex Bytecode in hexadecimal format.
	 * @param bytes
	 */
	private void runExpecting(String hex, byte... bytes) {
		runExpecting(parseHex(hex), bytes);
	}

	/**
	 * Overload of <code>runExpecting</code> where input specified as word array.
	 *
	 * @param words Bytecode as an array of ints.
	 * @param bytes
	 */
	private void runExpecting(int[] words, byte... bytes) {
		runExpecting(toBytes(words), bytes);
	}


	/**
	 * Run a bytecode program expecting it to raise an out-of-gas error.
	 *
	 * @param bytecode
	 */
	private void runOutOfGas(int[] words) {
		System.out.println("Excuting: " + Main.toHexString(toBytes(words)));
		// Execute the EVM
		Outcome r = new Main(new HashMap<>(),toBytes(words)).run();
		// FIXME: better reporting for out-of-gas.
		assert(r.getReturnData() == null);
	}

	/**
	 * Convert an array of Java ints into an array of bytes. This assumes that every
	 * int is within bounds for a byte.
	 *
	 * @param words
	 * @return
	 */
	private byte[] toBytes(int... words) {
		byte[] bytes = new byte[words.length];
		for(int i=0;i!=words.length;++i) {
			int ith = words[i];
			assertTrue(ith >= 0);
			assertTrue(ith <= 255);
			bytes[i] = (byte) ith;
		}
		return bytes;
	}

	/**
	 * Construct a 256bit representation (in big endian form) of an unsigned Java int.
	 * @param x
	 * @return
	 */
	private byte[] UINT256(int x) {
		if(x < 0) {
			throw new IllegalArgumentException("Argument cannot be negative");
		}
		byte[] bytes = new byte[32];
		bytes[31] = (byte) (x & 0xFF);
		bytes[30] = (byte) ((x >> 8) & 0xFF);
		bytes[29] = (byte) ((x >> 16) & 0xFF);
		bytes[28] = (byte) ((x >> 24) & 0xFF);
		return bytes;
	}

	/**
	 * Shift an array of bytes to the left a given amount.
	 *
	 * @param bytes
	 * @param k
	 * @return
	 */
	private byte[] shl(byte[] bytes, int k) {
		if (k <= 0) {
			throw new IllegalArgumentException();
		} else {
			byte[] r = new byte[bytes.length];
			for (int i = k; i < bytes.length; ++i) {
				r[i - k] = bytes[k];
			}
			return r;
		}
	}

	private byte[] not(byte[] bytes) {
		byte[] r = new byte[bytes.length];
		for (int i = 0; i < bytes.length; ++i) {
			r[i] = (byte) ~(bytes[i]);
		}
		return r;
	}
}
