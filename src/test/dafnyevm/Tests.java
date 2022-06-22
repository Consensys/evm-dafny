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

	/**
	 * Run a given sequence of bytecodes, expecting things to go OK and to produce
	 * the given output.
	 *
	 * @param bytecode
	 * @param bytes
	 */
	private void runExpecting(int[] bytecode, byte... bytes) {
		byte[] code = new byte[bytecode.length];
		for(int i=0;i!=bytecode.length;++i) {
			int ith = bytecode[i];
			assertTrue(ith >= 0);
			assertTrue(ith <= 255);
			code[i] = (byte) ith;
		}
		runExpecting(code, bytes);
	}

	private void runExpecting(byte[] bytecode, byte... bytes) {
		// Execute the EVM
		Outcome r = new Main(new HashMap<>(),bytecode).run();
		// Check we haven't reverted
		assertFalse(r.isRevert());
		// Check something was returned
		assertTrue(r.getReturnData() != null);
		// Ok!
		assertEquals(DafnySequence.fromBytes(bytes), r.getReturnData());
	}
}
