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

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.apache.commons.lang3.tuple.Pair;
import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import org.json.JSONTokener;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import dafnyevm.core.Account;
import dafnyevm.core.StateTest;
import dafnyevm.core.Trace;
import dafnyevm.core.Transaction;
import dafnyevm.util.Tracers;

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
	/**
	 * The directory containing the reference test test files.
	 */
	public final static Path FIXTURES_DIR = Path.of("fixtures");

	@ParameterizedTest
	@MethodSource("allTestFiles")
	public void tests(Path raw) throws IOException, JSONException {
		// Strip down to specific test details.
		Path test = raw.subpath(1, raw.getNameCount());
		String testName = test.getFileName().toString();
		testName = testName.substring(0,testName.indexOf('.'));
		Path testPath = test.getParent();
		// Read fixture JSON
		JSONObject fixture = readFixtureFile(testPath.resolve(testName + ".json"));
		// Read internal data
		List<Pair<StateTest.Outcome,Trace>> outcomes = readInternalStates(raw);
		// Run through tests
		for (String testname : JSONObject.getNames(fixture)) {
			List<Pair<StateTest.Outcome, Trace>> matches = selectOutcomes(outcomes, FORK, testname);
			JSONObject testfixture = fixture.getJSONObject(testname);
			runParameterisedTest(testname, matches, testfixture);
		}
	}

	/**
	 * Run a given parameterised test, and comparing against a known set of expected
	 * outcomes.
	 *
	 * @param testname
	 * @param outcomes
	 * @param testfixture
	 * @throws JSONException
	 */
	private void runParameterisedTest(String testname, List<Pair<StateTest.Outcome, Trace>> outcomes,
			JSONObject testfixture) throws JSONException {
		// Parse transaction template
		Transaction.Template txt = Transaction.Template.fromJSON(testfixture.getJSONObject("transaction"));
		// Parse world state
		Map<BigInteger, Account> worldstate = Main.parsePreState(testfixture.getJSONObject("pre"));
		// Parse state test info
		StateTest[] tests = Main.parsePostState(testfixture.getJSONObject("post")).get(FORK);
		assumeTrue(tests != null);
		// Sanity check outcomes matche tests
		assertEquals(tests.length, outcomes.size());
		// Compare every test against the expected outcome.
		int passed = 0;
		//
		for (int i = 0; i != outcomes.size(); ++i) {
			Pair<StateTest.Outcome, Trace> ith = outcomes.get(i);
			// Lookout for tests we must ignore
			if(isIgnored(tests[i].expect)) {
				System.out.println("*** IGNORING (" + tests[i].expect + "): " + testname + ", " + i);
			} else if(ith.getLeft().wasRunnable()) {
				List<Trace.Element> expected = ith.getRight().getElements();
				List<Trace.Element> actual = runActualTest(txt, tests[i], worldstate);
				// Now, compare traces
				assertEquals(expected, actual);
				passed = passed + 1;
			}
			// Signal test should be ignored.
			// assumeTrue(false);
		}
		// If there wasn't a single test that we could run, then let's mark this whole
		// test as "ignored" since that's effectively what we've done. This just helps
		// with reporting.
		assumeTrue(passed > 0);
	}

	private List<Trace.Element> runActualTest(Transaction.Template txt, StateTest test, Map<BigInteger, Account> worldstate) {
		List<Trace.Element> actual = new ArrayList<>();
		// Run test generating snapshot data.
		Main.runStateTest(txt,test,worldstate,new Tracers.Structured(actual));
		//
		return actual;
	}

	// Here we enumerate all available test cases.
	private static Stream<Path> allTestFiles() throws IOException {
		return readTestFiles(TESTS_DIR, n -> true);
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
	private static boolean isIgnored(StateTest.Expectation expect) {
		// NOTE: at the moment, the Dafny EVM does not support gas in any form and,
		// therefore, cannot detect out-of-gas errors. Thus, for now, we simply ignore
		// them.
		switch (expect) {
		case IntrinsicGas:
		case OutOfGas:
			return true;
		default:
			return false;
		}
	}

	/**
	 * A wrapper for a rather ugly list map. This basically selects all outcomes
	 * obtained for a given tests, using a given fork.
	 *
	 * @param outcomes
	 * @param fork The given fork.
	 * @param name The given test name.
	 * @return
	 */
	private static List<Pair<StateTest.Outcome, Trace>> selectOutcomes(List<Pair<StateTest.Outcome, Trace>> outcomes,
			String fork, String name) {
		return outcomes.stream().filter(p -> p.getLeft().fork.equals(FORK) && p.getLeft().name.equals(name))
				.collect(Collectors.toList());
	}

	// ======================================================================
	// Helpers
	// ======================================================================

	public static JSONObject readFixtureFile(Path file) throws IOException, JSONException {
		Path fixture = FIXTURES_DIR.resolve(file);
		// Read contents of fixture file
		String contents = Files.readString(fixture);
		// Convert fixture into JSON
		return new JSONObject(contents);
	}

	/**
	 * Construct the internal states for each test within a fixture. To be honest,
	 * this is not pretty and it would be nice to improve this.
	 *
	 * @param sfile
	 * @return
	 * @throws JSONException
	 * @throws IOException
	 */
	public static List<Pair<StateTest.Outcome, Trace>> readInternalStates(Path sfile)
			throws JSONException, IOException {
		Path file = Path.of(sfile.toString().replace(".results", ".states"));
		// Read results file.
		JSONArray outcomes = new JSONArray(Files.readString(sfile));
		// Read contents of fixture file
		FileInputStream fin = new FileInputStream(file.toFile());
		JSONTokener tok = new JSONTokener(fin);
		// Read all traces in.
		ArrayList<Pair<StateTest.Outcome, Trace>> res = new ArrayList<>();
		for (int i = 0; i != outcomes.length(); ++i) {
			StateTest.Outcome outcome = StateTest.Outcome.fromJSON(outcomes.getJSONObject(i));
			// NOTE: with geth, trace data is not produced for unsupported forks.
			Trace trace = null;
			if(outcome.wasRunnable()) {
				trace = parseTrace(tok);
			}
			res.add(Pair.of(outcome, trace));
		}
		// Done
		return res;
	}

	private static Trace parseTrace(JSONTokener tok) throws JSONException {
		List<Trace.Element> current = new ArrayList<>();
		// Add all JSON Objects (until there are no more)
		while (!tok.end()) {
			JSONObject obj = new JSONObject(tok);
			if (obj.has("stateRoot")) {
				return new Trace(current);
			} else {
				current.add(Trace.Element.fromJSON(obj));
			}
		}
		throw new IllegalArgumentException("invalid trace packet encountered");
	}

	// ======================================================================
	// Data sources
	// ======================================================================

	public static Stream<Path> readTestFiles(Path dir, Predicate<String> filter) throws IOException {
		ArrayList<Path> testcases = new ArrayList<>();
		//
		Files.walk(dir,3).forEach(f -> {
			if (f.toString().endsWith("results.json") && filter.test(f.getFileName().toString())) {
				// Determine the test name
				testcases.add(f);
			}
		});
		// Sort the result by filename
		Collections.sort(testcases);
		//
		return testcases.stream();
	}
}
