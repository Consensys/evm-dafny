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
import java.math.BigInteger;
import java.util.HashMap;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import dafny.DafnySequence;
import dafnyevm.DafnyEvm.SnapShot;
import dafnyevm.util.Hex;

import static dafnyevm.util.Bytecodes.*;

public class Tests {
	/**
	 * Enable to see additional debug information (e.g. internal states).
	 */
	private final boolean DEBUG = true;

	private final BigInteger DEFAULT_GAS = new BigInteger("10000000000");

	// ========================================================================
	// STOP / INVALID
	// ========================================================================

	@Test
	public void test_stop_01() {
		byte[] output = call(new int[] { STOP });
		assertArrayEquals(new byte[0], output);
	}

	@Test
	public void test_invalid_01() {
		invalidCall(new int[] { INVALID });
	}

	@Test
	public void test_invalid_02() {
		// Run of end of code sequence.
		invalidCall(new int[] { PUSH1, 0x01 });
	}

	// ========================================================================
	// PUSH, RETURN, POP
	// ========================================================================

	@Test
	public void test_push1_01() {
		byte[] output = call(new int[] { PUSH1, 0x00, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[0], output);
	}

	@Test
	public void test_push1_02() {
		byte[] output = call(new int[] { PUSH1, 0x01, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0 }, output);
	}

	@Test
	public void test_push2_01() {
		byte[] output = call(new int[] { PUSH2, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_pop_01() {
		byte[] output = call(new int[] { PUSH1, 0x02, PUSH1, 0x01, POP, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_pop_invalid_01() {
		// Insufficient operands
		invalidCall(new int[] { POP });
	}

	@Test
	public void test_revert_01() {
		byte[] output = revertingCall(new int[] { PUSH1, 0x00, PUSH1, 0x00, REVERT });
		assertArrayEquals(new byte[0], output);
	}

	@Test
	public void test_revert_02() {
		byte[] output = revertingCall(new int[] { PUSH1, 0x01, PUSH1, 0x00, REVERT });
		assertArrayEquals(new byte[] { 0 }, output);
	}

	@Test
	public void test_revert_03() {
		byte[] output = revertingCall(new int[] { PUSH2, 0x00, 0x02, PUSH1, 0x00, REVERT });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	// ========================================================================
	// MLOAD, MSTORE
	// ========================================================================

	@Test
	public void test_mstore_01() {
		// Check words stored in big endian format.
		byte[] output = call(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x1, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0 }, output);
	}

	@Test
	public void test_mstore_02() {
		// Check can return data from memory.
		byte[] output = call(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x7b), output);
	}

	@Test
	public void test_mstore_03() {
		// Check can return data from memory.
		byte[] output = call(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x4d7b), output);
	}

	@Test
	public void test_mload_01() {
		// Check can read and write data to memory
		byte[] output = call(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x00, MLOAD, PUSH1, 0x20, MSTORE, PUSH1, 0x20, PUSH1, 0x20, RETURN });
		assertArrayEquals(UINT256(0x4d7b), output);
	}

	// ========================================================================
	// MSTORE8
	// ========================================================================

	@Test
	public void test_mstore8_01() {
		// Check words stored in big endian format.
		byte[] output = call(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE8, PUSH1, 0x1, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0x7b }, output);
	}

	@Test
	public void test_mstore8_02() {
		// Check can return data from memory.
		byte[] output = call(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE8, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(shl(UINT256(0x7b), 31), output);
	}

	@Test
	public void test_mstore8_03() {
		// Check can return data from memory.
		byte[] output = call(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, MSTORE8, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(shl(UINT256(0x7b), 31), output);
	}

	// ========================================================================
	// ADD / SUB / DIV / MUL
	// ========================================================================

	@Test
	public void test_add_01() {
		// 2 + 1 => 3
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x2, ADD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3), output);
	}

	@Test
	public void test_sub_01() {
		// 3 - 1 => 2
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x3, SUB, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x2), output);
	}

	@Test
	public void test_sub_02() {
		// 0 - 6 => -6
		byte[] output = call(new int[] { PUSH1, 0x6, PUSH1, 0x0, SUB, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(not(UINT256(0x5)), output);
	}

	@Test
	public void test_mul_01() {
		// 2 * 3 => 6
		byte[] output = call(new int[] { PUSH1, 0x3, PUSH1, 0x2, MUL, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x6), output);
	}

	@Test
	public void test_div_01() {
		// 6 / 2 => 3
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x6, DIV, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3), output);
	}

	@Test
	public void test_sdiv_01() {
		// 6 / 2 => 3
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x6, SDIV, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3), output);
	}

	@Test
	public void test_sdiv_02() {
		// -6 / 2 => -3
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x6, PUSH1, 0x0, SUB, SDIV, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(not(UINT256(0x2)), output);
	}

	@Test
	public void test_sdiv_03() {
		// -6 / -2 => 3
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x6, PUSH1, 0x0, SUB, SDIV, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3), output);
	}

	@Test
	public void test_sdiv_04() {
		// -6 / 4 => -1
		byte[] output = call(new int[] { PUSH1, 0x4, PUSH1, 0x6, PUSH1, 0x0, SUB, SDIV, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(not(UINT256(0x0)), output);
	}

	@Test
	public void test_mod_01() {
		// 6 % 2 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x6, MOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_mod_02() {
		// 6 % 4 => 2
		byte[] output = call(new int[] { PUSH1, 0x4, PUSH1, 0x6, MOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x02), output);
	}

	@Test
	public void test_smod_01() {
		// 6 % 2 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x6, SMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_smod_02() {
		// 6 % 4 => 2
		byte[] output = call(new int[] { PUSH1, 0x4, PUSH1, 0x6, SMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x02), output);
	}

	@Test
	public void test_smod_03() {
		// -6 % 2 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x6, PUSH1, 0x0, SUB, SMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_smod_04() {
		// -6 % 4 => -2
		byte[] output = call(new int[] { PUSH1, 0x4, PUSH1, 0x6, PUSH1, 0x0, SUB, SMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(not(UINT256(0x01)), output);
	}

	@Test
	public void test_smod_05() {
		// -6 % -2 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x6, PUSH1, 0x0, SUB, SMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_smod_06() {
		// -6 % -4 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x6, PUSH1, 0x0, SUB, SMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_addmod_01() {
		// (2 + 1) % 8 => 3
		byte[] output = call(new int[] { PUSH1, 0x8, PUSH1, 0x1, PUSH1, 0x2, ADDMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3), output);
	}

	@Test
	public void test_addmod_02() {
		// (5 + 1) % 4 => 2
		byte[] output = call(new int[] { PUSH1, 0x4, PUSH1, 0x1, PUSH1, 0x5, ADDMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x2), output);
	}

	@Test
	public void test_mulmod_01() {
		// (2 * 3) % 8 => 6
		byte[] output = call(new int[] { PUSH1, 0x8, PUSH1, 0x3, PUSH1, 0x2, MULMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x6), output);
	}

	@Test
	public void test_mulmod_02() {
		// (2 * 3) % 4 => 2
		byte[] output = call(new int[] { PUSH1, 0x4, PUSH1, 0x3, PUSH1, 0x2, MULMOD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x2), output);
	}

	// ========================================================================
	// AND / OR / XOR / NOT
	// ========================================================================

	@Test
	public void test_and_01() {
		// 0b0001 & 0b0001  => 0b0001
		byte[] output = call(new int[] { PUSH1, 0b0001, PUSH1, 0b0001, AND, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b0001), output);
	}

	@Test
	public void test_and_02() {
		// 0b0001 & 0b0011  => 0b0001
		byte[] output = call(new int[] { PUSH1, 0b0011, PUSH1, 0b0001, AND, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b0001), output);
	}

	@Test
	public void test_and_03() {
		// 0b0101 & 0b0011  => 0b0001
		byte[] output = call(new int[] { PUSH1, 0b0011, PUSH1, 0b0101, AND, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b0001), output);
	}

	@Test
	public void test_or_01() {
		// 0b0001 | 0b0001  => 0b0001
		byte[] output = call(new int[] { PUSH1, 0b0001, PUSH1, 0b0001, OR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b0001), output);
	}

	@Test
	public void test_or_02() {
		// 0b0001 | 0b0011  => 0b0011
		byte[] output = call(new int[] { PUSH1, 0b0011, PUSH1, 0b0001, OR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b0011), output);
	}

	@Test
	public void test_or_03() {
		// 0b0101 | 0b0011  => 0b0111
		byte[] output = call(new int[] { PUSH1, 0b0011, PUSH1, 0b0101, OR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b0111), output);
	}

	@Test
	public void test_xor_01() {
		// 0b0001 ^ 0b0001  => 0b0000
		byte[] output = call(new int[] { PUSH1, 0b0001, PUSH1, 0b0001, XOR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b0000), output);
	}

	@Test
	public void test_xor_02() {
		// 0b0001 ^ 0b0011  => 0b0010
		byte[] output = call(new int[] { PUSH1, 0b0011, PUSH1, 0b0001, XOR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b0010), output);
	}

	@Test
	public void test_xor_03() {
		// 0b0101 ^ 0b0011  => 0b0110
		byte[] output = call(new int[] { PUSH1, 0b0011, PUSH1, 0b0101, XOR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b0110), output);
	}

	@Test
	public void test_not_01() {
		// ~0b00000101 => 0b11111010
		byte[] output = call(new int[] { PUSH1, 0b0101, NOT, PUSH1, 0x1F, MSTORE8, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0b11111010), output);
	}

	@Test
	public void test_not_02() {
		// ~0b00000101 => 0b11111010
		byte[] output = call(new int[] { PUSH1, 0b0101, NOT, PUSH1, 0x0, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(not(UINT256(0b00000101)), output);
	}

	@Test
	public void test_byte_01() {
		// Read byte 31 (0x1f) from 0x0102.
		byte[] output = call(new int[] { PUSH2, 0x01, 0x02, PUSH1, 0x1F, BYTE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x02), output);
	}

	@Test
	public void test_byte_02() {
		// Read byte 30 (0x1e) from 0x0102.
		byte[] output = call(new int[] { PUSH2, 0x01, 0x02, PUSH1, 0x1E, BYTE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x01), output);
	}

	@Test
	public void test_shl_01() {
		// 0xFE << 1 = 0x1FC
		byte[] output = call(new int[] { PUSH1, 0xFE, PUSH1, 0x1, SHL, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1FC), output);
	}

	@Test
	public void test_shl_02() {
		// 0xFE << 2 = 0x3F8
		byte[] output = call(new int[] { PUSH1, 0xFE, PUSH1, 0x2, SHL, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3F8), output);
	}

	@Test
	public void test_shl_03() {
		// 0xFE << 3 = 0x7F0
		byte[] output = call(new int[] { PUSH1, 0xFE, PUSH1, 0x3, SHL, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x7F0), output);
	}

	// Add more shift tests here!

	// ========================================================================
	// LT / GT / SLT / SGT / EQ / ISZERO
	// ========================================================================

	@Test
	public void test_lt_01() {
		// 2 < 1 = 0
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x2, LT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_lt_02() {
		// 1 < 2 = 1
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x1, LT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_lt_03() {
		// 2 < 2 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x2, LT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_gt_01() {
		// 2 > 1 => 1
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x2, GT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_gt_02() {
		// 1 > 2 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x1, GT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_gt_03() {
		// 2 > 2 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x2, GT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_slt_01() {
		// -2 < 1 => 1
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x2, PUSH1, 0x0, SUB, SLT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_slt_02() {
		// 1 < -2 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x1, SLT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_slt_03() {
		// -2 < -1 => 1
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, SUB, PUSH1, 0x2, PUSH1, 0x0, SUB, SLT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_slt_04() {
		// -1 < -2 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x1, PUSH1, 0x0, SUB, SLT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_sgt_01() {
		// -2 > 1 => 0
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x2, PUSH1, 0x0, SUB, SGT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_sgt_02() {
		// 1 > -2 => 1
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x1, SGT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_sgt_03() {
		// -2 > -1 => 0
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, SUB, PUSH1, 0x2, PUSH1, 0x0, SUB, SGT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_sgt_04() {
		// -1 > -2 => 1
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x1, PUSH1, 0x0, SUB, SGT, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_eq_01() {
		// 2 = 1 => 0
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x2, EQ, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_eq_02() {
		// 2 = 2 => 1
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x2, EQ, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_iszero_01() {
		// 2 = 0 => 0
		byte[] output = call(new int[] { PUSH1, 0x2, ISZERO, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_iszero_02() {
		// 0 = 0 => 1
		byte[] output = call(new int[] { PUSH1, 0x0, ISZERO, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}


	// ========================================================================
	// SLOAD, SSTORE
	// ========================================================================

	@Test
	public void test_sstore_01() {
		// test add11 from the reference tests
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x1, ADD, PUSH1, 0x00, SSTORE, STOP });
		assertArrayEquals(new byte[0], output);
	}

	@Test
	public void test_sstore_02() {
		byte[] output = call(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, SSTORE, PUSH1, 0x00, SLOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x4d7b), output);
	}

	// ========================================================================
	// CALLDATA
	// ========================================================================

	@Test
	public void test_calldatasize_01() {
		byte[] output = call(0, new byte[0],
				new int[] { CALLDATASIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_calldatasize_02() {
		byte[] output = call(0, new byte[1],
				new int[] { CALLDATASIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_calldatasize_03() {
		byte[] output = call(0, new byte[7],
				new int[] { CALLDATASIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x7), output);
	}

	@Test
	public void test_calldataload_01() {
		byte[] output = call(0, UINT256(0xab4f7b),
				new int[] { PUSH1, 0, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0xab4f7b));
	}

	@Test
	public void test_calldataload_02() {
		// Calldata has 31bytes, so CALLDATALOAD adds additional zero byte as lsb.
		byte[] output = call(0, new byte[] { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x74 },
				new int[] { PUSH1, 0, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x7400));
	}

	@Test
	public void test_calldataload_03() {
		// Calldata has 31bytes, so CALLDATALOAD adds two additional zero bytes.
		byte[] output = call(0, new byte[] { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x74 },
				new int[] { PUSH1, 0, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x740000));
	}

	@Test
	public void test_calldataload_04() {
		// Read from non-zero offset in calldata (which results in padding)
		byte[] output = call(0, UINT256(0xab4f7b),
				new int[] { PUSH1, 1, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0xab4f7b00L));
	}

	@Test
	public void test_calldataload_05() {
		// Load multiple items from calldata
		byte[] output = call(0, append(UINT256(0xab4f7b),UINT256(0x7c4ead)),
				new int[] { PUSH1, 0, CALLDATALOAD, PUSH1, 0x20, CALLDATALOAD, ADD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN});
		assertArrayEquals(output, UINT256(0xab4f7b + 0x7c4ead));
	}

	@Test
	public void test_calldatacopy_01() {
		// Copy call data into memory and return.
		byte[] output = call(0, UINT256(0xab4f7b),
				new int[] { PUSH1, 0x20, PUSH1, 0x0, PUSH1, 0x0, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0xab4f7b));
	}

	@Test
	public void test_calldatacopy_02() {
		// Partially copy call data into memory and return.
		byte[] output = call(0, UINT256(0xab4f7b),
				new int[] { PUSH1, 0x1F, PUSH1, 0x0, PUSH1, 0x0, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0xab4f00));
	}

	@Test
	public void test_calldatacopy_03() {
		// Copy call data into memory at non-zero offset and return.
		byte[] output = call(0, new byte[] { 0x4f, 0x7b },
				new int[] { PUSH1, 0x1, PUSH1, 0x1, PUSH1, 0x1F, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x7b));
	}

	@Test
	public void test_calldatacopy_04() {
		// Copy call data into memory at non-zero offset and return.
		byte[] output = call(0, new byte[] { 0x4f, 0x7b },
				new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x1F, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x4f));
	}

	@Test
	public void test_calldatacopy_05() {
		// Copy call data into memory at non-zero offset and return.
		byte[] output = call(0, new byte[] { 0x4f, 0x7b },
				new int[] { PUSH1, 0x1, PUSH1, 0x1, PUSH1, 0x1E, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x7b00));
	}

	@Test
	public void test_calldatacopy_06() {
		// Copy call data into memory at non-zero offset and return.
		byte[] output = call(0, new byte[] { 0x4f },
				new int[] { PUSH1, 0x2, PUSH1, 0x0, PUSH1, 0x1E, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x4f00));
	}

	// ========================================================================
	// DUP
	// ========================================================================

	@Test
	public void test_dup1_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, DUP1, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup2_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, DUP2, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup3_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, DUP3, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup4_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP4, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup5_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP5, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup6_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP6, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup7_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP7, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup8_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP8, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup9_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP9, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup10_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP10, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup11_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP11, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup12_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP12, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup13_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP13, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup14_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP14, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup15_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP15, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	@Test
	public void test_dup16_01() {
		byte[] output = call(new int[] { PUSH1, 0x3d, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, DUP16, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x3d), output);
	}

	// ========================================================================
	// SWAP
	// ========================================================================

	@Test
	public void test_swap1_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x2, SWAP1, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap2_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x2, SWAP2, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap3_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP3, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap4_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP4, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap5_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP5, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap6_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP6, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap7_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP7, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap8_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP8, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap9_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP9, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap10_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP10, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap11_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP11, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap12_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP12, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap13_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP13, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap14_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP14, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap15_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP15, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_swap16_01() {
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x0, PUSH1, 0x2, SWAP16, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	// ========================================================================
	// JUMP
	// ========================================================================

	@Test
	public void test_jump_01() {
		// Branch over invalid
		byte[] output = call(new int[] { PUSH1, 0x4, JUMP, INVALID, JUMPDEST, STOP });
		assertArrayEquals(new byte[0], output);
	}

	@Test
	public void test_jump_invalid_01() {
		// Invalid destination
		invalidCall(new int[] { PUSH1, 0x3, JUMP });
	}

	@Test
	public void test_jump_invalid_02() {
		// JUMPDEST required
		invalidCall(new int[] { PUSH1, 0x3, JUMP, STOP });
	}

	// ========================================================================
	// JUMPI
	// ========================================================================

	@Test
	public void test_jumpi_01() {
		// Condition branch (taken) over invalid
		byte[] output = call(new int[] { PUSH1, 0x01, PUSH1, 0x6, JUMPI, INVALID, JUMPDEST, STOP });
		assertArrayEquals(new byte[0], output);
	}

	@Test
	public void test_jumpi_02() {
		// Condition branch (not taken) avoids invalid
		byte[] output = call(new int[] { PUSH1, 0x00, PUSH1, 0x6, JUMPI, STOP, JUMPDEST, INVALID });
		assertArrayEquals(new byte[0], output);
	}

	@Test
	public void test_jumpi_03() {
		// Condition branch (not taken) doesn't require JUMPDEST.
		byte[] output = call(new int[] { PUSH1, 0x00, PUSH1, 0x6, JUMPI, STOP });
		assertArrayEquals(new byte[0], output);
	}

	@Test
	public void test_jumpi_invalid_01() {
		// Condition branch (taken) hits invalid
		invalidCall(new int[] { PUSH1, 0x00, PUSH1, 0x6, JUMPI, INVALID, JUMPDEST, STOP });
	}

	@Test
	public void test_jumpi_invalid_02() {
		// Condition branch (not taken) hits invalid
		invalidCall(new int[] { PUSH1, 0x01, PUSH1, 0x6, JUMPI, STOP, JUMPDEST, INVALID });
	}

	// ========================================================================
	// PC
	// ========================================================================

	@Test
	public void test_pc_01() {
		// PC = 0
		byte[] output = call(new int[] { PC, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_pc_02() {
		// PC = 1
		byte[] output = call(new int[] { JUMPDEST, PC, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_pc_03() {
		// PC = 2
		byte[] output = call(new int[] { PUSH1, 0x1, PC, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x2), output);
	}

	// ========================================================================
	// Misc
	// ========================================================================

	@Test
	public void test_highmemory_write_01() {
		// Check out-of-gas for high memory write.
		insufficientGasCall(new int[] {
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
		insufficientGasCall(new int[] {
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
	 * the given output (i.e. return data).
	 *
	 * @param from     Address this call is coming from.
	 * @param calldata Input data for the call.
	 * @param code     The EVM bytecode sequence to execute.
	 */
	private byte[] call(BigInteger from, BigInteger gas, byte[] calldata, byte[] code) {
		System.out.println("Excuting: " + Hex.toHexString(code));
		// Execute the EVM
		SnapShot r = new DafnyEvm(new HashMap<>(), code).call(from, gas, calldata);
		// Check we haven't reverted
		assertFalse(r.isRevert());
		// Check something was returned
		assertNotNull(r.getReturnData());
		// Ok!
		return toBytes(r.getReturnData());
	}

	private byte[] call(long from, byte[] calldata, int[] code) {
		BigInteger origin = BigInteger.valueOf(from);
		return call(origin, DEFAULT_GAS, calldata, toBytes(code));
	}

	/**
	 * Run a given sequence of bytecodes, expecting things to go OK and to produce
	 * the given output (i.e. return data). For simplicity, this variant assumes a
	 * default <code>origin</code> and empty <code>calldata</code>.
	 *
	 * @param code  The EVM bytecode sequence to execute.
	 * @param bytes Expected output data.
	 */
	private byte[] call(byte[] code) {
		return call(BigInteger.TEN, DEFAULT_GAS, new byte[0], code);
	}

	/**
	 * Run a given sequence of bytecodes, expecting things to go OK and to produce
	 * the given output (i.e. return data). For simplicity, this variant assumes a
	 * default <code>origin</code> and empty <code>calldata</code>.
	 *
	 * @param words Bytecode as an array of ints.
	 * @param bytes
	 */
	private byte[] call(int[] words) {
		return call(toBytes(words));
	}

	/**
	 * Run a given sequence of bytecodes, expecting things to go OK and to produce
	 * the given output.
	 *
	 * @param bytecode
	 * @param bytes
	 */
	private byte[] revertingCall(byte[] code) {
		System.out.println("Excuting: " + Hex.toHexString(code));
		// Execute the EVM
		SnapShot r = new DafnyEvm(new HashMap<>(), code).call(BigInteger.TEN, DEFAULT_GAS, new byte[0]);
		// Check we have reverted
		assertTrue(r.isRevert());
		// Check something was returned
		assertNotNull(r.getReturnData());
		// Ok!
		return toBytes(r.getReturnData());
	}

	/**
	 * Overload of <code>runExpecting</code> where input specified as word array.
	 *
	 * @param words Bytecode as an array of ints.
	 * @param bytes
	 */
	private byte[] revertingCall(int[] words) {
		return revertingCall(toBytes(words));
	}

	/**
	 * Run a bytecode program expecting to reach an invalid bytecode.
	 *
	 * @param code
	 * @param bytes
	 */
	private void invalidCall(int[] words) {
		// Execute the EVM
		SnapShot r = new DafnyEvm(new HashMap<>(),toBytes(words)).call(BigInteger.TEN, DEFAULT_GAS, new byte[0]);
		// Check expected outcome
		assert r.isInvalid();
	}

	/**
	 * Run a bytecode program expecting it to raise an out-of-gas error.
	 *
	 * @param bytecode
	 */
	private void insufficientGasCall(int[] words) {
		System.out.println("Excuting: " + Hex.toHexString(toBytes(words)));
		// Execute the EVM
		SnapShot r = new DafnyEvm(new HashMap<>(),toBytes(words)).call(BigInteger.TEN, DEFAULT_GAS, new byte[0]);
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
	 * Convert a dafny sequence into a sequence of raw bytes.
	 *
	 * @param seq
	 * @return
	 */
	private byte[] toBytes(DafnySequence<? extends Byte> seq) {
		byte[] bytes = new byte[seq.length()];
		for(int i=0;i!=seq.length();++i) {
			bytes[i] = seq.select(i);
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
	 * Construct a 256bit representation (in big endian form) of an unsigned Java long.
	 * @param x
	 * @return
	 */
	private byte[] UINT256(long x) {
		if(x < 0) {
			throw new IllegalArgumentException("Argument cannot be negative");
		}
		byte[] bytes = new byte[32];
		bytes[31] = (byte) (x & 0xFF);
		bytes[30] = (byte) ((x >> 8) & 0xFF);
		bytes[29] = (byte) ((x >> 16) & 0xFF);
		bytes[28] = (byte) ((x >> 24) & 0xFF);

		bytes[27] = (byte) ((x >> 32) & 0xFF);
		bytes[26] = (byte) ((x >> 40) & 0xFF);
		bytes[25] = (byte) ((x >> 48) & 0xFF);
		bytes[24] = (byte) ((x >> 56) & 0xFF);
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

	private byte[] append(byte[] lhs, byte[] rhs) {
		byte[] res = new byte[lhs.length + rhs.length];
		System.arraycopy(lhs, 0, res, 0, lhs.length);
		System.arraycopy(rhs, 0, res, lhs.length, rhs.length);
		return res;
	}
}
