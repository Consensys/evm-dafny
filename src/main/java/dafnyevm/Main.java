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

import org.apache.commons.cli.*;
import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import dafnyevm.util.Tracers;
import dafnyevm.DafnyEvm.SnapShot;
import dafnyevm.DafnyEvm.Tracer;
import dafnyevm.core.Transaction;
import dafnyevm.core.Account;
import dafnyevm.core.StateTest;
import dafnyevm.util.Hex;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

public class Main {
	/**
	 * Fork which (for now) I'm assuming we are running on. All others are ignored.
	 */
	public final static String FORK = "Berlin";

	private static final Option[] OPTIONS = new Option[] {
			new Option("input", true, "Input data for the transaction."),
			new Option("sender", true, "The transaction origin."),
			new Option("debug", false, "Generate trace output"),
			new Option("json", false, "Generate JSON output conforming to EIP-3155"),
			new Option("statetest", false, "Executes the given state tests")
	};

	public static CommandLine parseCommandLine(String[] args) {
		// Configure command-line options.
		Options options = new Options();
		for(Option o : OPTIONS) { options.addOption(o); }
		CommandLineParser parser = new DefaultParser();
		// use to read Command Line Arguments
		HelpFormatter formatter = new HelpFormatter();  // // Use to Format
		try {
			return parser.parse(options, args);  //it will parse according to the options and parse option value
		} catch (ParseException e) {
			System.out.println(e.getMessage());
			formatter.printHelp("dafnyevm", options);
			System.exit(1);
			return null;
		}
	}

	public static void main(String[] args) throws IOException, JSONException {
		// Parse command-line arguments.
		CommandLine cmd = parseCommandLine(args);
		// Dispatch to requested command
		if(cmd.hasOption("statetest")) {
			runStateTest(cmd);
		} else {
			runArbitraryBytecode(cmd);
		}
	}

	public static void runArbitraryBytecode(CommandLine cmd) {
		// Extract transaction sender.
		BigInteger sender = Hex.toBigInt(cmd.getOptionValue("sender", "0xdeff"));
		// Extract call data (if applicable)
		byte[] calldata = Hex.toBytes(cmd.getOptionValue("input", "0x"));
		// Continue processing remaining arguments.
		String[] args = cmd.getArgs();
		//
		// Parse input string
		byte[] bytes = Hex.toBytes(args[0]);
		// Construct EVM
		DafnyEvm evm = new DafnyEvm(new HashMap<>(), bytes);
		//
		evm.setTracer(determineTracer(cmd));
		// Execute the EVM
		evm.call(sender, calldata);
	}

	public static Tracer determineTracer(CommandLine cmd) {
		if (cmd.hasOption("json")) {
			return new Tracers.JSON();
		} else if (cmd.hasOption("debug")) {
			return new Tracers.Debug();
		} else {
			return new Tracers.Default();
		}
	}

	public static void runStateTest(CommandLine cmd) throws IOException, JSONException {
		Tracer tracer = determineTracer(cmd);
		String[] args = cmd.getArgs();
		// Iterate each test one at a time.
		for(String test : args) {
			// Read contents of test file
			String contents = Files.readString(Path.of(test));
			// Convert into JSON
			JSONObject json = new JSONObject(contents);
			// Run the test
			for(String testname : JSONObject.getNames(json)) {
				runStateTest(testname, FORK, tracer, json.getJSONObject(testname));
			}
		}
	}

	public static void runStateTest(String name, String fork, Tracer tracer, JSONObject json) throws JSONException {
		// Parse transaction template
		Transaction.Template txt = Transaction.Template.fromJSON(json.getJSONObject("transaction"));
		// Parse world state
		Map<BigInteger, Account> pre = parsePreState(json.getJSONObject("pre"));
		// Parse state test info
		Map<String, StateTest[]> post = parsePostState(json.getJSONObject("post"));
		//
		for (StateTest test : post.get(fork)) {
			runStateTest(txt, test, pre, tracer);
		}
	}

	public static void runStateTest(Transaction.Template txt, StateTest test, Map<BigInteger, Account> worldstate,
			Tracer tracer) {
		// FIXME: the following is hack to workaround the fact that the DafnyEvm
		// currently does not have a concept of the "world state".
		Transaction tx = txt.instantiate(test.indexes);
		byte[] code;
		Map<BigInteger, BigInteger> storage;
		if (tx.to != null) {
			// Normal situation. We are calling a contract account and we need to run its
			// code.
			storage = worldstate.get(tx.to).storage;
			code = worldstate.get(tx.to).code;
		} else {
			// In this case, we have an empty "to" field. Its not clear exactly what this
			// means, but I believe we can imagine it as something like the contract
			// creation account. Specifically, the code to execute is stored within the
			// transaction data.
			code = tx.data;
			storage = new HashMap<>();
		}
		// Construct EVM
		DafnyEvm evm = new DafnyEvm(storage, code).setTracer(tracer);
		// Run the transaction!
		evm.call(tx.sender, tx.data);
	}

	public static Map<BigInteger, Account> parsePreState(JSONObject json) throws JSONException {
		HashMap<BigInteger, Account> world = new HashMap<>();
		for (String addr : JSONObject.getNames(json)) {
			JSONObject contents = json.getJSONObject(addr);
			BigInteger hexAddr = Hex.toBigInt(addr);
			world.put(hexAddr, Account.fromJSON(contents));
		}
		return world;
	}

	public static Map<String, StateTest[]> parsePostState(JSONObject json) throws JSONException {
		HashMap<String, StateTest[]> forks = new HashMap<>();
		for (String fork : JSONObject.getNames(json)) {
			JSONArray tests = json.getJSONArray(fork);
			StateTest[] sts = new StateTest[tests.length()];
			for (int i = 0; i != sts.length; ++i) {
				sts[i] = StateTest.fromJSON(tests.getJSONObject(i));
			}
			forks.put(fork, sts);
		}
		return forks;
	}
}
