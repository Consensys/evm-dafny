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
import java.util.Arrays;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import static dafnyevm.DafnyEvm.DEFAULT_ORIGIN;
import static dafnyevm.DafnyEvm.DEFAULT_RECEIVER;
import dafnyevm.DafnyEvm.Account;
import dafnyevm.DafnyEvm.State;
import dafnyevm.util.Hex;

import static dafnyevm.util.Bytecodes.*;

public class Tests {

	// ========================================================================
	// 0s: Stop and Arithmetic Operations
	// ========================================================================

	@Test
	public void test_stop_01() {
		byte[] output = call(new int[] { STOP });
		assertArrayEquals(new byte[0], output);
	}

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

	@Test
	public void test_exp_01() {
		// 0^0 == 1
		byte[] output = call(new int[] { PUSH1, 0x0, PUSH1, 0x0, EXP, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_exp_02() {
		// 2^0 == 1
		byte[] output = call(new int[] { PUSH1, 0x0, PUSH1, 0x2, EXP, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_exp_03() {
		// 1^1 == 1
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x1, EXP, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_exp_04() {
		// 2^1 == 2
		byte[] output = call(new int[] { PUSH1, 0x1, PUSH1, 0x2, EXP, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x2), output);
	}

	@Test
	public void test_exp_05() {
		// 2^2 == 4
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x2, EXP, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x4), output);
	}

	@Test
	public void test_exp_06() {
		// 2^3 == 8
		byte[] output = call(new int[] { PUSH1, 0x3, PUSH1, 0x2, EXP, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x8), output);
	}

	@Test
	public void test_exp_07() {
		// 4^3 == 64
		byte[] output = call(new int[] { PUSH1, 0x3, PUSH1, 0x4, EXP, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x40), output);
	}

	// ========================================================================
	// 10s: Comparison & Bitwise Logic
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

	@Test
	public void test_shr_01() {
		// 0x1FC >> 1 = 0xFE
		byte[] output = call(new int[] { PUSH2, 0x1, 0xFC, PUSH1, 0x1, SHR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0xFE), output);
	}

	@Test
	public void test_shr_02() {
		// 0x3F8 >> 2 = 0xFE
		byte[] output = call(new int[] { PUSH2, 0x3, 0xF8, PUSH1, 0x2, SHR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0xFE), output);
	}

	@Test
	public void test_shr_03() {
		// 0x7F0 >> 3 = 0xFE
		byte[] output = call(new int[] { PUSH2, 0x7, 0xF0, PUSH1, 0x3, SHR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0xFE), output);
	}

	@Test
	public void test_sar_01() {
		// (0 - 0x2) >> 1 = -0x1
		byte[] output = call(new int[] { PUSH1, 0x2, PUSH1, 0x0, SUB, PUSH1, 0x1, SAR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(INT256(-0x1), output);
	}

	@Test
	public void test_sar_02() {
		// 0x1FC >> 1 = 0xFE
		byte[] output = call(new int[] { PUSH2, 0x1, 0xFC, PUSH1, 0x1, SAR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0xFE), output);
	}

	@Test
	public void test_sar_03() {
		// (0 - 0x1FC) >> 1 = -0xFE
		byte[] output = call(new int[] { PUSH2, 0x1, 0xFC, PUSH1, 0x0, SUB, PUSH1, 0x1, SAR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(INT256(-0xFE), output);
	}

	@Test
	public void test_sar_04() {
		// (0 - 0x3F8) >> 2 = -0xFE
		byte[] output = call(new int[] { PUSH2, 0x3, 0xF8, PUSH1, 0x0, SUB, PUSH1, 0x2, SAR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(INT256(-0xFE), output);
	}

	@Test
	public void test_sar_05() {
		// (0 - 0x7F0) >> 3 = -0xFE
		byte[] output = call(new int[] { PUSH2, 0x7, 0xF0, PUSH1, 0x0, SUB, PUSH1, 0x3, SAR, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(INT256(-0xFE), output);
	}

	// ========================================================================
	// 30s: Environmental Information
	// ========================================================================

	@Test
	public void test_calldatasize_01() {
		DafnyEvm tx = new DafnyEvm().from(0);
		byte[] output = call(tx, new int[] { CALLDATASIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_calldatasize_02() {
		DafnyEvm tx = new DafnyEvm().from(0).data(new byte[1]);
		byte[] output = call(tx, new int[] { CALLDATASIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x1), output);
	}

	@Test
	public void test_calldatasize_03() {
		DafnyEvm tx = new DafnyEvm().from(0).data(new byte[7]);
		byte[] output = call(tx, new int[] { CALLDATASIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0x7), output);
	}

	@Test
	public void test_calldataload_01() {
		DafnyEvm tx = new DafnyEvm().from(0).data(UINT256(0xab4f7b));
		byte[] output = call(tx, new int[] { PUSH1, 0, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0xab4f7b));
	}

	@Test
	public void test_calldataload_02() {
		// Calldata has 31bytes, so CALLDATALOAD adds additional zero byte as lsb.
		DafnyEvm tx = new DafnyEvm().from(0).data(
				new byte[] { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x74 });
		byte[] output = call(tx, new int[] { PUSH1, 0, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x7400));
	}

	@Test
	public void test_calldataload_03() {
		// Calldata has 31bytes, so CALLDATALOAD adds two additional zero bytes.
		DafnyEvm tx = new DafnyEvm().from(0).data(
				new byte[] { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x74 });
		byte[] output = call(tx, new int[] { PUSH1, 0, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x740000));
	}

	@Test
	public void test_calldataload_04() {
		// Read from non-zero offset in calldata (which results in padding)
		DafnyEvm tx = new DafnyEvm().from(0).data(UINT256(0xab4f7b));
		byte[] output = call(tx, new int[] { PUSH1, 1, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0xab4f7b00L));
	}

	@Test
	public void test_calldataload_05() {
		// Load multiple items from calldata
		DafnyEvm tx = new DafnyEvm().from(0).data(append(UINT256(0xab4f7b), UINT256(0x7c4ead)));
		byte[] output = call(tx, new int[] { PUSH1, 0, CALLDATALOAD, PUSH1, 0x20, CALLDATALOAD, ADD, PUSH1, 0x00,
				MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output, UINT256(0xab4f7b + 0x7c4ead));
	}

	@Test
	public void test_calldatacopy_01() {
		// Copy call data into memory and return.
		DafnyEvm tx = new DafnyEvm().from(0).data(UINT256(0xab4f7b));
		byte[] output = call(tx, new int[] { PUSH1, 0x20, PUSH1, 0x0, PUSH1, 0x0, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0xab4f7b));
	}

	@Test
	public void test_calldatacopy_02() {
		// Partially copy call data into memory and return.
		DafnyEvm tx = new DafnyEvm().from(0).data(UINT256(0xab4f7b));
		byte[] output = call(tx, new int[] { PUSH1, 0x1F, PUSH1, 0x0, PUSH1, 0x0, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0xab4f00));
	}

	@Test
	public void test_calldatacopy_03() {
		// Copy call data into memory at non-zero offset and return.
		DafnyEvm tx = new DafnyEvm().from(0).data(new byte[] { 0x4f, 0x7b });
		byte[] output = call(tx, new int[] { PUSH1, 0x1, PUSH1, 0x1, PUSH1, 0x1F, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x7b));
	}

	@Test
	public void test_calldatacopy_04() {
		// Copy call data into memory at non-zero offset and return.
		DafnyEvm tx = new DafnyEvm().from(0).data(new byte[] { 0x4f, 0x7b });
		byte[] output = call(tx, new int[] { PUSH1, 0x1, PUSH1, 0x0, PUSH1, 0x1F, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x4f));
	}

	@Test
	public void test_calldatacopy_05() {
		// Copy call data into memory at non-zero offset and return.
		DafnyEvm tx = new DafnyEvm().from(0).data(new byte[] { 0x4f, 0x7b });
		byte[] output = call(tx, new int[] { PUSH1, 0x1, PUSH1, 0x1, PUSH1, 0x1E, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x7b00));
	}

	@Test
	public void test_calldatacopy_06() {
		// Copy call data into memory at non-zero offset and return.
		DafnyEvm tx = new DafnyEvm().from(0).data(new byte[] { 0x4f });
		byte[] output = call(tx, new int[] { PUSH1, 0x2, PUSH1, 0x0, PUSH1, 0x1E, CALLDATACOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(output,UINT256(0x4f00));
	}

	@Test
	public void test_address_01() {
		// Check address == DEFAULT_RECEIVER
		byte[] output = call(new int[] { ADDRESS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(DEFAULT_RECEIVER.intValueExact()), output);
	}

	@Test
	public void test_origin_01() {
		// Check origin == DEFAULT_ORIGIN
		byte[] output = call(new int[] { ORIGIN, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(DEFAULT_ORIGIN.intValueExact()), output);
	}

	@Test
	public void test_caller_01() {
		// Check caller == DEFAULT_ORIGIN
		byte[] output = call(new int[] { CALLER, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(DEFAULT_ORIGIN.intValueExact()), output);
	}

	@Test
	public void test_callvalue_01() {
		// Check callvalue == 0 (i.e. default)
		byte[] output = call(new int[] { CALLVALUE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(0), output);
	}

	@Test
	public void test_callvalue_02() {
		// Check callvalue == suplied value
		DafnyEvm tx = new DafnyEvm().value(BigInteger.TEN);
		byte[] output = call(tx, new int[] { CALLVALUE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(10), output);
	}

	@Test
	public void test_codesize_01() {
		byte[] output = call(new int[] { CODESIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(9), output);
	}

	@Test
	public void test_codesize_02() {
		byte[] output = call(new int[] { CODESIZE, PUSH2, 0x00, 0x00, POP, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(13), output);
	}

	@Test
	public void test_codecopy_01() {
		// Check can copy code (with padding)
		byte[] output = call(new int[] { PUSH1, 0x20, PUSH1, 0x00, PUSH1, 0x00, CODECOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(Hex.toBytes("0x6020600060003960206000F30000000000000000000000000000000000000000"), output);
	}

	@Test
	public void test_codecopy_02() {
		// Check can copy code (with padding)
		byte[] output = call(new int[] { PUSH1, 0x20, PUSH1, 0x01, PUSH1, 0x00, CODECOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(Hex.toBytes("0x20600160003960206000F3000000000000000000000000000000000000000000"), output);
	}

	@Test
	public void test_codecopy_03() {
		// Check can copy code (with padding)
		byte[] output = call(new int[] { PUSH1, 0x20, PUSH1, 0x00, PUSH1, 0x01, CODECOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(Hex.toBytes("0x006020600060013960206000F300000000000000000000000000000000000000"), output);
	}

	@Test
	public void test_codecopy_04() {
		// Check can copy code (with padding)
		byte[] output = call(new int[] { PUSH1, 0x08, PUSH1, 0x00, PUSH1, 0x00, CODECOPY, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(Hex.toBytes("0x6008600060003960000000000000000000000000000000000000000000000000"), output);
	}

	@Test
	public void test_gasprice_01() {
		// Check gas price == 1
		byte[] output = call(new int[] { GASPRICE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(1), output);
	}

	// ========================================================================
	// 50s: Stack, Memory, Storage and Flow Operations
	// ========================================================================

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
	public void test_mstore_04() {
		// Check memory expansion from mstore
		byte[] output = call(new int[] { PUSH1, 0x15, PUSH1, 31, MSTORE, MSIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x0, RETURN });
		assertArrayEquals(UINT256(0x40), output);
	}

	@Test
	public void test_mstore_05() {
		// Check memory expansion from mstore
		byte[] output = call(new int[] { PUSH1, 0x7F, PUSH1, 31, MSTORE, MSIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x0, RETURN });
		assertArrayEquals(UINT256(0x40), output);
	}

	@Test
	public void test_mstore_06() {
		// Check memory expansion from mstore
		byte[] output = call(new int[] { PUSH1, 0x7F, PUSH1, 32, MSTORE, MSIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x0, RETURN });
		assertArrayEquals(UINT256(0x40), output);
	}

	@Test
	public void test_mstore_07() {
		// Check memory expansion from mstore
		byte[] output = call(new int[] { PUSH1, 0x7F, PUSH1, 33, MSTORE, MSIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x0, RETURN });
		assertArrayEquals(UINT256(0x60), output);
	}

	@Test
	public void test_mload_01() {
		// Check can read and write data to memory
		byte[] output = call(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x00, MLOAD, PUSH1, 0x20, MSTORE, PUSH1, 0x20, PUSH1, 0x20, RETURN });
		assertArrayEquals(UINT256(0x4d7b), output);
	}

	@Test
	public void test_mload_02() {
		// Check memory expansion from mload
		byte[] output = call(new int[] { PUSH1, 0, MLOAD, POP, MSIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x0, RETURN });
		assertArrayEquals(UINT256(0x20), output);
	}

	@Test
	public void test_mload_03() {
		// Check memory expansion from mload
		byte[] output = call(new int[] { PUSH1, 15, MLOAD, POP, MSIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x0, RETURN });
		assertArrayEquals(UINT256(0x40), output);
	}

	@Test
	public void test_mload_04() {
		// Check memory expansion from mload
		byte[] output = call(new int[] { PUSH1, 31, MLOAD, POP, MSIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x0, RETURN });
		assertArrayEquals(UINT256(0x40), output);
	}

	@Test
	public void test_mload_05() {
		// Check memory expansion from mload
		byte[] output = call(new int[] { PUSH1, 32, MLOAD, MSIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x0, RETURN });
		assertArrayEquals(UINT256(0x40), output);
	}

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

	@Test
	public void test_msize_01() {
		// Check memory expansion from mload
		byte[] output = call(new int[] { MSIZE, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x20, RETURN });
		assertArrayEquals(UINT256(0x0), output);
	}

	@Test
	public void test_gas_01() {
		// Check cost of GAS bytecode.
		byte[] output = call(new int[] { GAS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(DafnyEvm.DEFAULT_GAS.longValueExact() - 2), output);
	}

	@Test
	public void test_gas_02() {
		byte[] output = call(new int[] { PUSH1, 0x00, GAS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(DafnyEvm.DEFAULT_GAS.longValueExact() - 5), output);
	}

	@Test
	public void test_gas_03() {
		byte[] output = call(new int[] { PUSH1, 0x00, POP, GAS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(DafnyEvm.DEFAULT_GAS.longValueExact() - 7), output);
	}

	@Test
	public void test_gas_04() {
		byte[] output = call(new int[] { PUSH1, 0x01, PUSH1, 0x0, MSTORE, GAS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(DafnyEvm.DEFAULT_GAS.longValueExact() - 14), output);
	}

	@Test
	public void test_gas_05() {
		// 3 + 3 + 3 + (3 * 3) + 2
		byte[] output = call(new int[] { PUSH1, 0x01, PUSH1, 0x40, MSTORE, GAS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(DafnyEvm.DEFAULT_GAS.longValueExact() - 20), output);
	}

	@Test
	public void test_gas_06() {
		// 16415 / 32 = 513
		// (513 * 513) / 512 = 514
		// -------------------------------
		// 3 + 3 + 3 + (3 * 513 + 514) + 2
		byte[] output = call(new int[] { PUSH1, 0x01, PUSH2, 0x40, 0x00, MSTORE, GAS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		assertArrayEquals(UINT256(DafnyEvm.DEFAULT_GAS.longValueExact() - 2064), output);
	}

// NOTE: Following should be uncommented when gas calculation for MLOAD is implemented.
//
//	@Test
//	public void test_gas_07() {
//		byte[] output = call(new int[] { PUSH1, 0x01, PUSH1, 0x0, MLOAD, GAS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
//		assertArrayEquals(UINT256(DafnyEvm.DEFAULT_GAS.longValueExact() - 14), output);
//	}
//
//	@Test
//	public void test_gas_08() {
//		// 3 + 3 + 3 + (3 * 3) + 2
//		byte[] output = call(new int[] { PUSH1, 0x01, PUSH1, 0x40, MLOAD, GAS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
//		assertArrayEquals(UINT256(DafnyEvm.DEFAULT_GAS.longValueExact() - 20), output);
//	}
//
//	@Test
//	public void test_gas_09() {
//		// 16415 / 32 = 513
//		// (513 * 513) / 512 = 514
//		// -------------------------------
//		// 3 + 3 + 3 + (3 * 513 + 514) + 2
//		byte[] output = call(new int[] { PUSH1, 0x01, PUSH2, 0x40, 0x00, MLOAD, GAS, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
//		assertArrayEquals(UINT256(DafnyEvm.DEFAULT_GAS.longValueExact() - 2064), output);
//	}

	// ========================================================================
	// 60s & 70s: Push Operations
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
	public void test_push3_01() {
		byte[] output = call(new int[] { PUSH3, 0x00, 0x00, 0x03, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0, 0 }, output);
	}

	@Test
	public void test_push4_01() {
		byte[] output = call(new int[] { PUSH4, 0x00, 0x00, 0x00, 0x04, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0, 0, 0 }, output);
	}

	@Test
	public void test_push5_01() {
		byte[] output = call(new int[] { PUSH5, 0x00, 0x00, 0x00, 0x00, 0x05, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0, 0, 0, 0 }, output);
	}

	@Test
	public void test_push6_01() {
		byte[] output = call(new int[] { PUSH6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push7_01() {
		byte[] output = call(new int[] { PUSH7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push8_01() {
		byte[] output = call(new int[] { PUSH8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push9_01() {
		byte[] output = call(new int[] { PUSH9, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push10_01() {
		byte[] output = call(new int[] { PUSH10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push11_01() {
		byte[] output = call(new int[] { PUSH11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push12_01() {
		byte[] output = call(new int[] { PUSH12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push13_01() {
		byte[] output = call(new int[] { PUSH13, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push14_01() {
		byte[] output = call(new int[] { PUSH14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push15_01() {
		byte[] output = call(new int[] { PUSH15, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push16_01() {
		byte[] output = call(new int[] { PUSH16, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push17_01() {
		byte[] output = call(new int[] { PUSH17, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push18_01() {
		byte[] output = call(new int[] { PUSH18, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push19_01() {
		byte[] output = call(new int[] { PUSH19, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push20_01() {
		byte[] output = call(new int[] { PUSH20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push21_01() {
		byte[] output = call(new int[] { PUSH21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push22_01() {
		byte[] output = call(new int[] { PUSH22, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push23_01() {
		byte[] output = call(new int[] { PUSH23, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push24_01() {
		byte[] output = call(new int[] { PUSH24, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push25_01() {
		byte[] output = call(new int[] { PUSH25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push26_01() {
		byte[] output = call(new int[] { PUSH26, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push27_01() {
		byte[] output = call(new int[] { PUSH27, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push28_01() {
		byte[] output = call(new int[] { PUSH28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push29_01() {
		byte[] output = call(new int[] { PUSH29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push30_01() {
		byte[] output = call(new int[] { PUSH30, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push31_01() {
		byte[] output = call(new int[] { PUSH31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	@Test
	public void test_push32_01() {
		byte[] output = call(new int[] { PUSH32, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, PUSH1, 0x00, RETURN });
		assertArrayEquals(new byte[] { 0, 0 }, output);
	}

	// ========================================================================
	// 80s: Duplicate Operations
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
	// 90s: Exchange Operations
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
	// F0s: System Operations
	// ========================================================================

	/**
	 * Address of sub contract to use in these tests.
	 */
	private static final BigInteger CONTRACT_1 = Hex.toBigInt("0xccc");

	static {
		assertFalse(CONTRACT_1.equals(DEFAULT_RECEIVER));
	}

	@Test
	public void test_call_01() {
		// Absolutely minimal contract call which does nothing, and the caller then
		// returns the (successful) exit code.
		DafnyEvm tx = new DafnyEvm().put(CONTRACT_1, new Account(toBytes(STOP)));
		byte[] output = call(tx, new int[] {
				// Make contract call to 0xccc with gas 0xffff
				PUSH1, 0x0, DUP1, DUP1, DUP1, DUP1, PUSH2, 0xc, 0xcc, PUSH2, 0xff, 0xff, CALL,
				// Write exit code to memory and return.
				PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		//
		assertArrayEquals(UINT256(1), output);
	}

	@Test
	public void test_call_02() {
		// Contract call which raises an exception, and the subsequence exit code is
		// then returned by the caller.
		DafnyEvm tx = new DafnyEvm().put(CONTRACT_1, new Account(toBytes(INVALID)));
		//
		byte[] output = call(tx, new int[] {
				// Make contract call to 0xccc with gas 0xffff
				PUSH1, 0x0, DUP1, DUP1, DUP1, DUP1, PUSH2, 0xc, 0xcc, PUSH2, 0xff, 0xff, CALL,
				// Write exit code to memory and return.
				PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		//
		assertArrayEquals(UINT256(0), output);
	}

	@Test
	public void test_call_03() {
		// Contract call which reverts, and the subsequence exit code is then returned
		// by the caller.
		DafnyEvm tx = new DafnyEvm().put(CONTRACT_1, new Account(toBytes(PUSH1, 0x00, DUP1, REVERT)));
		byte[] output = call(tx, new int[] {
				// Make contract call to 0xccc with gas 0xffff
				PUSH1, 0x0, DUP1, DUP1, DUP1, DUP1, PUSH2, 0xc, 0xcc, PUSH2, 0xff, 0xff, CALL,
				// Write exit code to memory and return.
				PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN });
		//
		assertArrayEquals(UINT256(0), output);
	}

	@Test
	public void test_call_04() {
		// Contract call which returns "0x123", which the caller then itself returns.
		DafnyEvm tx = new DafnyEvm().put(CONTRACT_1,
				new Account(toBytes(PUSH2, 0x1, 0x23, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN)));
		byte[] output = call(tx, new int[] {
				// Make contract call to 0xccc with gas 0xffff, providing 32bytes for the return
				// data at address 0.
				PUSH1, 0x20, PUSH1, 0x00, DUP1, DUP1, DUP1, PUSH2, 0xc, 0xcc, PUSH2, 0xff, 0xff, CALL,
				// Return memory and return.
				PUSH1, 0x20, PUSH1, 0x00, RETURN });
		//
		assertArrayEquals(UINT256(0x123), output);
	}

	@Test
	public void test_call_05() {
		// Contract call passing "0x123" as call data which is then returned, and
		// subsequently the caller then itself returns that.
		DafnyEvm tx = new DafnyEvm().put(CONTRACT_1,
				new Account(toBytes(PUSH1, 0x00, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN)));

		byte[] output = call(tx, new int[] {
				// Write 0x123 to address 0x20
				PUSH2, 0x1, 0x23, PUSH1, 0x20, MSTORE,
				// Make contract call to 0xccc with gas 0xffff, providing 32bytes for the return
				// data at address 0.
				PUSH1, 0x20, PUSH1, 0x00, PUSH1, 0x20, DUP1, PUSH1, 0x0, PUSH2, 0xc, 0xcc, PUSH2, 0xff, 0xff, CALL,
				// Return memory and return.
				PUSH1, 0x20, PUSH1, 0x00, RETURN });
		//
		assertArrayEquals(UINT256(0x123), output);
	}

	@Test
	public void test_call_06() {
		// Contract call passing "0x123" as call data which is then returned. However,
		// the caller only request 31 bytes of return data which it then subsequently
		// returns (ending up in a truncated result).
		DafnyEvm tx = new DafnyEvm().put(CONTRACT_1,
				new Account(toBytes(PUSH1, 0x00, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN)));

		byte[] output = call(tx, new int[] {
				// Write 0x123 to address 0x20
				PUSH2, 0x1, 0x23, PUSH1, 0x20, MSTORE,
				// Make contract call to 0xccc with gas 0xffff, providing 32bytes for the return
				// data at address 0.
				PUSH1, 0x1F, PUSH1, 0x00, PUSH1, 0x20, DUP1, PUSH1, 0x0, PUSH2, 0xc, 0xcc, PUSH2, 0xff, 0xff, CALL,
				// Return memory and return.
				PUSH1, 0x20, PUSH1, 0x00, RETURN });
		//
		assertArrayEquals(UINT256(0x100), output);
	}

	@Test
	public void test_call_07() {
		// Contract call passing "0x123" as call data which is then returned with the
		// last byte truncated. Whilst the caller requested the full 32 bytes of return
		// data, it will end up with a truncated result.
		DafnyEvm tx = new DafnyEvm().put(CONTRACT_1,
				new Account(toBytes(PUSH1, 0x00, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x1F, PUSH1, 0x00, RETURN)));

		byte[] output = call(tx, new int[] {
				// Write 0x123 to address 0x20
				PUSH2, 0x1, 0x23, PUSH1, 0x20, MSTORE,
				// Make contract call to 0xccc with gas 0xffff, providing 32bytes for the return
				// data at address 0.
				PUSH1, 0x20, PUSH1, 0x00, PUSH1, 0x20, DUP1, PUSH1, 0x0, PUSH2, 0xc, 0xcc, PUSH2, 0xff, 0xff, CALL,
				// Return memory and return.
				PUSH1, 0x20, PUSH1, 0x00, RETURN });
		//
		assertArrayEquals(UINT256(0x100), output);
	}

	@Test
	public void test_call_08() {
		// Contract call passing "0x123" as call data which is then returned. However,
		// the caller only sends 31 bytes of return data, but it then subsequently
		// returns 32bytes (ending up in a truncated result).
		DafnyEvm tx = new DafnyEvm().put(CONTRACT_1,
				new Account(toBytes(PUSH1, 0x00, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN)));

		byte[] output = call(tx, new int[] {
				// Write 0x123 to address 0x20
				PUSH2, 0x1, 0x23, PUSH1, 0x20, MSTORE,
				// Make contract call to 0xccc with gas 0xffff, providing 32bytes for the return
				// data at address 0.
				PUSH1, 0x20, PUSH1, 0x00, PUSH1, 0x1F, PUSH1, 0x20, PUSH1, 0x0, PUSH2, 0xc, 0xcc, PUSH2, 0xff, 0xff, CALL,
				// Return memory and return.
				PUSH1, 0x20, PUSH1, 0x00, RETURN });
		//
		assertArrayEquals(UINT256(0x100), output);
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

	@Test
	public void test_invalid_01() {
		invalidCall(new int[] { INVALID });
	}

	@Test
	public void test_invalid_02() {
		// Run off end of code sequence.
		byte[] output = call(new int[] { PUSH1, 0x01 });
		assertArrayEquals(new byte[0], output);
	}

	// ========================================================================
	// Misc
	// ========================================================================

	/**
	 * Run a given sequence of bytecodes, expecting things to go OK and to produce
	 * the given output (i.e. return data). For simplicity, this variant assumes a
	 * default <code>origin</code> and empty <code>calldata</code>.
	 *
	 * @param code The EVM bytecode sequence to execute.
	 */
	private byte[] call(int[] words) {
		return call(new DafnyEvm(),words);
	}

	private byte[] call(DafnyEvm context, int[] words) {
		byte[] code = toBytes(words);
		return context.put(DEFAULT_RECEIVER, new Account(code)).call().getReturnData();
	}

	/**
	 * Run a given sequence of bytecodes, expecting things to go OK and to produce
	 * the given output.
	 *
	 * @param bytecode
	 * @param bytes
	 */
	private byte[] revertingCall(int[] words) {
		byte[] code = toBytes(words);
		State<?> r = new DafnyEvm().put(DEFAULT_RECEIVER,new Account(code)).call();
		// Check we have reverted as expected
		assertTrue(r instanceof State.Revert);
		// Check something was returned
		assertNotNull(r.getReturnData());
		// Ok!
		return r.getReturnData();
	}

	/**
	 * Run a bytecode program expecting to reach an invalid bytecode.
	 *
	 * @param code
	 * @param bytes
	 */
	private void invalidCall(int[] words) {
		byte[] code = toBytes(words);
		State r = new DafnyEvm().put(DEFAULT_RECEIVER,new Account(code)).from(DEFAULT_RECEIVER).call();
		// Check exception was thrown as expected.
		assert r instanceof State.Invalid;
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
	 * Construct a 256bit representation (in big endian form) of a signed Java int.
	 * @param x
	 * @return
	 */
	private byte[] INT256(int x) {
		if (x >= 0) {
			return UINT256(x);
		} else {
			byte[] bytes = new byte[32];
			Arrays.fill(bytes, 0, 31, (byte) 0xff);
			bytes[31] = (byte) (x & 0xFF);
			bytes[30] = (byte) ((x >> 8) & 0xFF);
			bytes[29] = (byte) ((x >> 16) & 0xFF);
			bytes[28] = (byte) ((x >> 24) & 0xFF);
			return bytes;
		}
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
