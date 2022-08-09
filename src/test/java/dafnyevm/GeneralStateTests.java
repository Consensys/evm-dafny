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

import static org.junit.jupiter.api.Assumptions.assumeTrue;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import org.json.JSONException;
import org.json.JSONObject;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import dafny.DafnyMap;
import dafny.DafnySequence;
import dafnyevm.util.Bytecodes;
import evmtools.core.Trace;
import evmtools.core.TraceTest;
import evmtools.core.Transaction;
import evmtools.core.WorldState;
import evmtools.util.Hex;

/**
 * A test runner for executing the <code>GeneralStateTests</code> provided as
 * part of the Ethereum Reference tests (see
 * <a href="https://github.com/ethereum/tests/">here</a>). The test runner works
 * by combining two pieces of information for each tests:
 *
 * <ul>
 * <li><b>Test Fixture</b>. This is the (filled) tests provided by the Ethereum
 * reference tests, and accessible from this repository within the
 * <code>fixtures/</code> directory (which is a submodule).</li>
 * <li><b>Internal State</b>. This internal state information generated from
 * running the corresponding fixture using an existing tool, such as Geth's
 * `evm` command-line tool. This internal state supplements the test fixture
 * which information about the EVM internals during execution of the test (e.g.
 * the value of the stack or memory after executing each bytecode). This data is
 * stored within the <code>tests/</code> directory, where the layout follows
 * that of the <code>fixtures</code> directory.</li>
 * </ul>
 *
 * This test runner is "driven" by the test files stored within the
 * <code>tests/</code>. That means a test is only run when there is a
 * corresponding entry in this file.
 *
 * @author David J. Pearce
 *
 */
public class GeneralStateTests {
	/**
	 * Fork which (for now) I'm assuming we are running on. All others are ignored.
	 */
	public final static String FORK = "Berlin";
	/**
	 * The directory containing the test files.
	 */
	public final static Path TESTS_DIR = Path.of("tests");

	@ParameterizedTest
	@MethodSource("allTestFiles")
	public void tests(TraceTest.Instance instance) throws IOException, JSONException {
		if(isIgnored(instance.getExpectation())) {
			// Force test to be ignored.
			assumeTrue(false);
		} else {
			Transaction tx = instance.getTransaction();
			WorldState ws = instance.getWorldState();
			byte[] code;
			Map<BigInteger, BigInteger> storage;
			if (tx.to != null) {
				// Normal situation. We are calling a contract account and we need to run its
				// code.
				storage = ws.get(tx.to).storage;
				code = ws.get(tx.to).code;
			} else {
				// In this case, we have an empty "to" field. Its not clear exactly what this
				// means, but I believe we can imagine it as something like the contract
				// creation account. Specifically, the code to execute is stored within the
				// transaction data.
				code = tx.data;
				storage = new HashMap<>();
			}
			// Construct EVM
			ArrayList<Trace.Element> elements = new ArrayList<>();
			StructuredTracer tracer = new StructuredTracer(elements);
			DafnyEvm evm = new DafnyEvm(storage, code).setTracer(tracer).setGasPrice(tx.gasPrice);
			// Run the transaction!
			evm.call(tx.to, tx.sender, tx.gasLimit, tx.value, tx.data);
			//
			Trace tr = new Trace(elements);
			// Finally check for equality.
			assertEquals(instance.getTrace(),tr);
		}
	}

	// Here we enumerate all available test cases.
	private static Stream<TraceTest.Instance> allTestFiles() throws IOException {
		return readTestFiles(TESTS_DIR);
	}

	/**
	 * Determine whether this test should be ignore because (for some reason) it is
	 * considered out of scope of the Dafny EVM. This might be due to missing
	 * features (which, eventually, will be implemeted). Or, it might because of
	 * something more fundamental (e.g. something this testing framework cannot
	 * handle).
	 *
	 * @param expect
	 * @return
	 */
	private static boolean isIgnored(Transaction.Expectation expect) {
		// NOTE: at the moment, the Dafny EVM does not support gas in any form and,
		// therefore, cannot detect out-of-gas errors. Thus, for now, we simply ignore
		// them.
		switch (expect) {
		case IntrinsicGas:
			return true;
		default:
			return false;
		}
	}

	// ======================================================================
	// Helpers
	// ======================================================================

	public static JSONObject readTestFile(Path file) throws IOException, JSONException {
		Path fixture = TESTS_DIR.resolve(file);
		// Read contents of fixture file
		String contents = Files.readString(fixture);
		// Convert fixture into JSON
		return new JSONObject(contents);
	}

	// ======================================================================
	// Data sources
	// ======================================================================

	public static Stream<TraceTest.Instance> readTestFiles(Path dir) throws IOException {
		ArrayList<Path> testfiles = new ArrayList<>();
		//
		Files.walk(dir).forEach(f -> {
			if (f.toString().endsWith(".json")) {
				testfiles.add(f);
			}
		});
		// Instantiate each state test into one or more
		return streamTestsFromFiles(testfiles.stream());
	}

	/**
	 * Given a stream of filenames convert this into a stream of test instances. The
	 * reason for doing this is that it can be done lazily, therefore reducing
	 * overall memory footprint.
	 *
	 * @param files
	 * @return
	 */
	private static Stream<TraceTest.Instance> streamTestsFromFiles(Stream<Path> files) {
		return files.flatMap(f -> {
			try {
				// Read contents of fixture file
				String contents = Files.readString(f);
				// Convert fixture into JSON
				JSONObject json = new JSONObject(contents);
				// Parse into one or more tests
				ArrayList<TraceTest.Instance> instances = new ArrayList<>();
				for (String test : JSONObject.getNames(json)) {
					TraceTest tt = TraceTest.fromJSON(test, json.getJSONObject(test));
					if (tt.hasInstances(FORK)) {
						// Add all instances
						instances.addAll(tt.getInstances(FORK));
					}
				}
				return instances.stream();
			} catch (JSONException e) {
				System.out.println("Problem parsing file into JSON (" + f + ")");
				return null;
			} catch (IOException e) {
				System.out.println("Problem reading file (" + f + ")");
				return null;
			} catch (Exception e) {
				System.out.println("Problem reading file (" + f + ")");
				e.printStackTrace();
				return null;
			}
		});
	}

	public static class StructuredTracer extends DafnyEvm.TraceAdaptor {
		private final List<Trace.Element> out;

		public StructuredTracer(List<Trace.Element> out) {
			this.out = out;
		}

		@Override
		public void step(DafnyEvm.SnapShot state) {
			int pc = state.getPC().intValueExact();
			int op = state.getOpcode();
			// NOTE: to make traces equivalent with Geth we cannot appear to have "executed"
			// the invalid bytecode.
			if(op != Bytecodes.INVALID) {
				byte[] memory = DafnySequence.toByteArray((DafnySequence) state.getMemory());
				BigInteger[] stack = (BigInteger[]) state.getStack().toRawArray();
				DafnyMap<? extends BigInteger, ? extends BigInteger> rawStorage = state.getStorage();
				HashMap<BigInteger, BigInteger> storage = new HashMap<>();
				for (BigInteger addr : storage.keySet()) {
					storage.put(addr, rawStorage.get(addr));
				}
				// NOTE: we need to reverse the stack elements here as the Dafny stores them
				// internally with index at zero.
				Collections.reverse(Arrays.asList(stack));
				//
				out.add(new Trace.Step(pc, op, stack, memory, storage));
			} else {
				System.out.println("SKIPPING");
			}
		}

		@Override
		public void end(byte[] output, BigInteger gasUsed) {
			out.add(new Trace.Returns(output));
		}

		@Override
		public void revert(byte[] output, BigInteger gasUsed) {
			out.add(new Trace.Reverts(output));
		}

		@Override
		public void exception(BigInteger gasUsed) {
			out.add(new Trace.Exception());
		}
	}
}
