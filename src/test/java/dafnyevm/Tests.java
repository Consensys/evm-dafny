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
import static dafnyevm.util.Bytecodes.*;


public class Tests {

	@Test
	public void test_01() {
		runExpecting(new int[] { STOP });
	}

	@Test
	public void test_02() {
		// Return nothing.
		runExpecting(new int[] { PUSH1, 0x00, PUSH1, 0x00, RETURN });
	}

	@Test
	public void test_03() {
		// Return 1 zero byte
		runExpecting(new int[] { PUSH1, 0x01, PUSH1, 0x00, RETURN }, new byte[] { 0 });
	}

	@Test
	public void test_04() {
		// Check words stored in big endian format.
		runExpecting(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x1, PUSH1, 0x00, RETURN }, new byte[] { 0 });
	}

	@Test
	public void test_05() {
		// Check can return data from memory.
		runExpecting(new int[] { PUSH1, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT32(0x7b));
	}

	@Test
	public void test_06() {
		// Check can return data from memory.
		runExpecting(new int[] { PUSH2, 0x4d, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT32(0x4d7b));
	}

	@Test
	public void test_07() {
		// Check can add!
		runExpecting(new int[] { PUSH1, 0x1, PUSH1, 0x2, ADD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN }, UINT32(0x3));
	}

	@Test
	public void test_08() {
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
	public void test_10() {
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
	private void runExpecting(int[] words, byte... bytes) {
		System.out.println("Excuting: " + Main.toHexString(toBytes(words)));
		// Execute the EVM
		Outcome r = new Main(new HashMap<>(),toBytes(words)).run();
		// Check we haven't reverted
		assertFalse(r.isRevert());
		// Check something was returned
		assertTrue(r.getReturnData() != null);
		// Ok!
		assertEquals(DafnySequence.fromBytes(bytes), r.getReturnData());
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
	private byte[] UINT32(int x) {
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
}
