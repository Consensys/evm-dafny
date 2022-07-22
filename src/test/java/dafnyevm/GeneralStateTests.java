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

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.stream.Stream;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import org.json.JSONTokener;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import dafnyevm.core.Trace;
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
		Map<String,List<Trace>> internal = readInternalStates(raw);
		// Run the test
		for (String testname : JSONObject.getNames(fixture)) {
			if(internal.containsKey(testname)) {
				List<Trace> expected = internal.get(testname);
				List<Trace> actual = new ArrayList<>();
				// Run the tests generating all the snapshots.
				Main.runStateTest(testname, new Tracers.Structured(actual), fixture.getJSONObject(testname));
				// Now, compare traces
				assertEquals(expected,actual);
			} else {
				// Signal test should be ignored.
				assumeTrue(false);
			}
		}
	}

	// Here we enumerate all available test cases.
	private static Stream<Path> allTestFiles() throws IOException {
		return readTestFiles(TESTS_DIR, n -> true);
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
	public static Map<String, List<Trace>> readInternalStates(Path sfile)
			throws JSONException, IOException {
		//
		Path file = Path.of(sfile.toString().replace(".results", ".states"));
		// Read results file.
		JSONArray schema = new JSONArray(Files.readString(sfile));
		// Read contents of fixture file
		FileInputStream fin = new FileInputStream(file.toFile());
		JSONTokener tok = new JSONTokener(fin);
		List<List<Trace>> packets = new ArrayList<>();
		List<Trace> current = new ArrayList<>();
		// Add all JSON Objects (until there are no more)
		while (!tok.end()) {
			try {
				JSONObject obj = new JSONObject(tok);
				if (obj.has("output")) {
					// Terminal
					current.add(Trace.fromJSON(obj));
					packets.add(current);
					current = new ArrayList<>();
				} else if(obj.has("stateRoot")) {
					packets.add(current);
					current = new ArrayList<>();
				} else {
					current.add(Trace.fromJSON(obj));
				}
			} catch (JSONException e) {
				break;
			}
		}
		// Now, put it all back together.
		Map<String, List<Trace>> res = new HashMap<>();
		int index = 0;
		for(int i=0;i!=schema.length();++i) {
			JSONObject ith = schema.getJSONObject(i);
			if(ith.getBoolean("pass")) {
				if(ith.getString("fork").equals(FORK)) {
					res.put(ith.getString("name"), packets.get(index));
				}
				index = index + 1;
			}
		}
		// Done
		return res;
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
