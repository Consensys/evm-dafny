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
import org.json.JSONException;
import org.json.JSONObject;

import evmtools.core.StateTest;
import evmtools.util.Hex;
import dafnyevm.util.StateTests;
import dafnyevm.util.Tracers;
import dafnyevm.DafnyEvm.Tracer;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

public class Main {
	/**
	 * Fork which (for now) I'm assuming we are running on. All others are ignored.
	 */
	public final static String FORK = "Berlin";

	private static final Option[] OPTIONS = new Option[] {
			new Option("Receiver", true, "The transaction receiver (default 0xabc)."),
			new Option("sender", true, "The transaction origin  (default 0xdef)."),
			new Option("debug", false, "Generate trace output"),
			new Option("json", false, "Generate JSON output conforming to EIP-3155"),
			new Option("input", true, "Call data for the transaction (default none)."),
			new Option("value", true, "call value to use (default 0x0)"),
			new Option("gas", true, "gas limit for the evm (default 0x10000000000)"),
			new Option("gasPrice", true, "gas price to use (default 0x1)"),
			new Option("fork", true, "Specificy fork"),
			// Top-level commands
            new Option("run", false, "Execute arbitrary bytecode"),
			new Option("proof", false, "Generate Dafy proof for bytecode given as argument"),
			new Option("statetest", false, "Executes the given state test")
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
		} else if(cmd.hasOption("run")) {
		    runArbitraryBytecode(cmd);
		} else {
		    System.out.println("error: must provide either --run or --statetest or --proof argument!");
		}
	}

	public static void runArbitraryBytecode(CommandLine cmd) {
		// Extract transaction sender.
		BigInteger sender = Hex.toBigInt(cmd.getOptionValue("sender", "0xabc"));
		// Extract transaction receiver.
		BigInteger receiver = Hex.toBigInt(cmd.getOptionValue("receiver", "0xdef"));
		// Extract call value (if applicable)
		BigInteger callValue = Hex.toBigInt(cmd.getOptionValue("value", "0x0"));
		// Extract call data (if applicable)
		byte[] calldata = Hex.toBytes(cmd.getOptionValue("input", "0x"));
		//
		BigInteger gas = Hex.toBigInt(cmd.getOptionValue("gas", "0x10000000000"));
		//
		BigInteger gasPrice = Hex.toBigInt(cmd.getOptionValue("gasPrice", "0x1"));
		// Continue processing remaining arguments.
		String[] args = cmd.getArgs();
		//
		// Parse input string
		byte[] bytes = Hex.toBytes(args[0]);
		// Construct EVM
		DafnyEvm evm = new DafnyEvm().tracer(determineTracer(cmd)).gasPrice(gasPrice).create(receiver, bytes)
				.to(receiver).sender(sender).origin(sender).gas(gas).data(calldata).value(callValue);
		// Execute the EVM
		evm.call();
	}

	/**
     * Run a state test from the command-line. To do this, we have to load and parse
     * the JSON file representing the state test, then setup the configuration and
     * run the EVM.
     *
     * @param cmd
	 * @throws IOException
	 * @throws JSONException
     */
    public static void runStateTest(CommandLine cmd) throws IOException, JSONException {
        String fork = cmd.getOptionValue("fork", "Berlin");
        // Determine filename of state test
        String filename = cmd.getArgs()[0];
        // Read its contents as a string.
        String contents = Files.readString(Path.of(filename));
        // Convert contents into JSON
        JSONObject json = new JSONObject(contents);
        // Parse JSON into one or more StateTests
        List<StateTest> tests = StateTest.fromJSON(json);
        // Determine tracer to use
        Tracer tracer = determineTracer(cmd);
        // Iterate each individual test
        for (StateTest t : tests) {
            // Extract instances for specific fork
            for (StateTest.Instance i : t.getInstances(fork)) {
                StateTests.runInstance(i.getName(), i.getEnvironment(), i.getWorldState(), i.instantiate(), tracer);
            }
        }
    }

	public static Tracer determineTracer(CommandLine cmd) {
		if (cmd.hasOption("json")) {
			return new Tracers.JSON();
		} else if (cmd.hasOption("debug")) {
			return new Tracers.Debug();
		} else {
			return DafnyEvm.DEFAULT_TRACER;
		}
	}
}
