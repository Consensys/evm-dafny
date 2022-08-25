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

import java.io.File;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import org.apache.commons.lang3.tuple.Pair;
import org.json.JSONException;
import org.json.JSONObject;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import dafnyevm.DafnyEvm.State;
import dafnyevm.DafnyEvm.State.CallContinue;
import dafnyevm.util.Bytecodes;
import evmtools.core.Trace;
import evmtools.core.TraceTest;
import evmtools.core.Transaction;
import evmtools.core.WorldState;

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
	 * The set of tests which are (for various reasons) currently ignored. Each
	 * ignored test must be given a reason for this.
	 */
	public final static List<String> IGNORES = Arrays.asList( //
			"stExample/invalidTr.json", // Intrinsic Gas.
			"VMTests/vmArithmeticTest/exp.json", // #195
			"VMTests/vmArithmeticTest/expPower256Of256.json", // #195
			"VMTests/vmArithmeticTest/signextend.json", // #194
			"stMemoryTest/bufferSrcOffset.json", // #199
			"stMemoryTest/calldatacopy_dejavu.json", // Should raise exception
			"stMemoryTest/codecopy_dejavu.json", // Should raise exception
			"stMemoryTest/memCopySelf.json", // #200
			"stMemoryTest/mload_dejavu.json", // Should raise exception
			"stMemoryTest/mstore_dejavu.json", // Should raise exception
			"stMemoryTest/mstroe8_dejavu.json", // Should raise exception
			"stMemoryTest/oog.json", // Various problems
			"stMemoryTest/stackLimitGas_1023.json", // #201
			"stMemoryTest/stackLimitGas_1024.json", // #201
			"stMemoryTest/stackLimitGas_1025.json", // #201
			//
			"stCallCodes/callcall_00.json", // #202
			"stCallCodes/callcallcall_000.json", // #202
			//
			"stCallCodes/callcall_00_OOGE.json", // OOG?
			"stCallCodes/callcall_00_OOGE_valueTransfer.json", // OOG?
			//
			"stCallCodes/callcall_00_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcallcall_000_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcallcall_000_SuicideMiddle.json", // SELFDESTRUCT
			"stCallCodes/callcallcallcode_001_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcallcallcode_001_SuicideMiddle.json",// SELFDESTRUCT
			//
			"stCallCodes/callcallcall_ABCB_RECURSIVE.json", // #218
			"stCallCodes/callcallcallcode_001.json", //
			"stCallCodes/callcallcallcode_ABCB_RECURSIVE.json", // #218
			"stCallCodes/callcallcode_01.json", // ?
			"stCallCodes/callcallcode_01_SuicideEnd.json", // ?
			"stCallCodes/callcallcodecall_010.json", // ?
			"stCallCodes/callcallcodecall_010_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcallcodecall_010_SuicideMiddle.json", // SELFDESTRUCT
			"stCallCodes/callcallcodecall_ABCB_RECURSIVE.json", // #218
			"stCallCodes/callcallcodecallcode_011.json", // ?
			"stCallCodes/callcallcodecallcode_011_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcallcodecallcode_011_SuicideMiddle.json", // SELFDESTRUCT
			"stCallCodes/callcallcodecallcode_ABCB_RECURSIVE.json", // #218
			"stCallCodes/callcodecall_10.json", // ?
			"stCallCodes/callcodecall_10_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcodecallcall_100.json", // ?
			"stCallCodes/callcodecallcall_100_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcodecallcall_100_SuicideMiddle.json", // SELFDESTRUCT
			"stCallCodes/callcodecallcall_ABCB_RECURSIVE.json", // ?
			"stCallCodes/callcodecallcallcode_101.json", // ?
			"stCallCodes/callcodecallcallcode_101_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcodecallcallcode_101_SuicideMiddle.json", // SELFDESTRUCT
			"stCallCodes/callcodecallcallcode_ABCB_RECURSIVE.json", // ?
			"stCallCodes/callcodecallcode_11.json", // ?
			"stCallCodes/callcodecallcode_11_SuicideEnd.json", // ?
			"stCallCodes/callcodecallcodecall_110.json", // ?
			"stCallCodes/callcodecallcodecall_110_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcodecallcodecall_110_SuicideMiddle.json", // SELFDESTRUCT
			"stCallCodes/callcodecallcodecall_ABCB_RECURSIVE.json", // ?
			"stCallCodes/callcodecallcodecallcode_111.json", // ?
			"stCallCodes/callcodecallcodecallcode_111_SuicideEnd.json", // SELFDESTRUCT
			"stCallCodes/callcodecallcodecallcode_111_SuicideMiddle.json", // SELFDESTRUCT
			"stCallCodes/callcodecallcodecallcode_ABCB_RECURSIVE.json", // ?
			"stCallCodes/callcodeEmptycontract.json", // ?
			//
			"stCallCodes/callcodeDynamicCode2SelfCall.json", // CREATE
			"stCallCodes/callcodeDynamicCode.json",  // CREATE
			"stCallCodes/callcodeInInitcodeToEmptyContract.json", // CREATE
			"stCallCodes/callcodeInInitcodeToExisContractWithVTransferNEMoney.json", // CREATE
			"stCallCodes/callcodeInInitcodeToExistingContract.json", // CREATE
			"stCallCodes/callcodeInInitcodeToExistingContractWithValueTransfer.json", // CREATE
			"stCallCodes/call_OOG_additionalGasCosts2.json", // Should raise exception
			"stCallCodes/touchAndGo.json", // ?
			//
			"vmTests/random.json", // #200
			"vmTests/sha3.json", // SHA3?
			"vmTests/calldatacopy.json", // CALLDATACOPY?
			"vmTests/calldatasize.json", // CALLDATASIZE?
			"vmTests/suicide.json", // SELFDESTRUCT
			"vmTests/envInfo.json", // CODECOPY
			"vmTests/blockInfo.json", // COINBASE
			"vmLogTest/log0.json", // #206
			"vmLogTest/log1.json", // #206
			"vmLogTest/log2.json", // #206
			"vmLogTest/log3.json", // #206
			"vmLogTest/log4.json", // #206
			"vmIOandFlowOperations/jump.json", // DELEGATECALL
			"vmIOandFlowOperations/mstore8.json", // DELEGATECALL
			"vmIOandFlowOperations/mload.json", // DELEGATECALL
			"vmIOandFlowOperations/codecopy.json", // DELEGATECALL
			"vmIOandFlowOperations/loopsConditionals.json", // DELEGATECALL
			"vmIOandFlowOperations/msize.json", // DELEGATECALL
			"vmIOandFlowOperations/pop.json", // DELEGATECALL
			"vmIOandFlowOperations/return.json", // DELEGATECALL
			"vmIOandFlowOperations/gas.json", // DELEGATECALL
			"vmIOandFlowOperations/pc.json", // DELEGATECALL
			"vmIOandFlowOperations/mstore.json", // DELEGATECALL
			"vmIOandFlowOperations/jumpToPush.json", // #200
			"vmIOandFlowOperations/jumpi.json", // DELEGATECALL
			"vmIOandFlowOperations/sstore_sload.json", // #200
			"dummy"
	);

	@ParameterizedTest
	@MethodSource("allTestFiles")
	public void tests(Pair<Path,TraceTest.Instance> pair) throws IOException, JSONException {
		final TraceTest.Instance instance = pair.getRight();
		//
		if(isIgnored(pair.getLeft())) {
			// Force test to be ignored.
			assumeTrue(false);
		} else {
			Transaction tx = instance.getTransaction();
			// Figure out an appopriate receiver
			BigInteger to = tx.to != null ? tx.to : DafnyEvm.DEFAULT_RECEIVER;
			// Convert world state over.
			Map<BigInteger,DafnyEvm.Account> ws = buildWorldState(tx,instance.getWorldState());
			// Construct EVM
			ArrayList<Trace.Element> elements = new ArrayList<>();
			StructuredTracer tracer = new StructuredTracer(elements);
			DafnyEvm evm = new DafnyEvm().tracer(tracer).gasPrice(tx.gasPrice).to(to).from(tx.sender)
					.origin(tx.sender).gas(tx.gasLimit).value(tx.value).data(tx.data).putAll(ws);
			// Run the transaction!
			evm.call();
			//
			Trace tr = new Trace(elements);
			// Finally check for equality.
			assertEquals(instance.getTrace(),tr);
		}
	}

	/**
	 * Apply
	 * @param st
	 * @param evm
	 * @return
	 */
	public Map<BigInteger,DafnyEvm.Account> buildWorldState(Transaction tx, WorldState ws) {
		HashMap<BigInteger,DafnyEvm.Account> dws = new HashMap<>();
		// Initialise world statew
		for(Map.Entry<BigInteger, evmtools.core.Account> e : ws.entrySet()) {
			evmtools.core.Account acct = e.getValue();
			dws.put(e.getKey(),new DafnyEvm.Account(acct.code,acct.balance,acct.storage));
		}
		// Finally, configure transaction receiver (if necessary).
		if (tx.to == null) {
			// In this case, we have an empty "to" field. Its not clear exactly what this
			// means, but I believe we can imagine it as something like the contract
			// creation account. Specifically, the code to execute is stored within the
			// transaction data.
			dws.put(DafnyEvm.DEFAULT_RECEIVER,new DafnyEvm.Account(tx.data, BigInteger.ZERO, new HashMap<>()));
		}
		return dws;
	}

	// Here we enumerate all available test cases.
	private static Stream<Pair<Path,TraceTest.Instance>> allTestFiles() throws IOException {
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
	private static boolean isIgnored(Path path) {
		// Normalise path notation for platofmr
		String p = path.toString().replace(File.separator, "/");
		// Check whether this matches an IGNORE or not.
		for (int i = 0; i != IGNORES.size(); ++i) {
			String ith = IGNORES.get(i);
			if (p.endsWith(ith)) {
				return true;
			}
		}
		return false;
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

	public static Stream<Pair<Path,TraceTest.Instance>> readTestFiles(Path dir) throws IOException {
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
	private static Stream<Pair<Path,TraceTest.Instance>> streamTestsFromFiles(Stream<Path> files) {
		return files.flatMap(f -> {
			try {
				// Read contents of fixture file
				String contents = Files.readString(f);
				// Convert fixture into JSON
				JSONObject json = new JSONObject(contents);
				// Parse into one or more tests
				ArrayList<Pair<Path, TraceTest.Instance>> instances = new ArrayList<>();
				for (String test : JSONObject.getNames(json)) {
					TraceTest tt = TraceTest.fromJSON(test, json.getJSONObject(test));
					if (tt.hasInstances(FORK)) {
						// Add all instances
						for (TraceTest.Instance i : tt.getInstances(FORK)) {
							instances.add(Pair.of(f, i));
						}
					}
				}
				return instances.stream();
			} catch (JSONException e) {
				e.printStackTrace();
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
		public void step(DafnyEvm.State.Ok state) {
			int pc = state.getPC().intValueExact();
			int op = state.getOpcode();
			// NOTE: to make traces equivalent with Geth we cannot appear to have "executed"
			// the invalid bytecode.
			if(op != Bytecodes.INVALID) {
				byte[] memory = state.getMemory();
				BigInteger[] stack = (BigInteger[]) state.getStack();
				// FIXME: this is a hack until such time as Geth actually reports storage.
				//Map<BigInteger, BigInteger> storage = state.getStorage();
				Map<BigInteger, BigInteger> storage = new HashMap<>();
				out.add(new Trace.Step(pc, op, stack, memory, storage));
			} else {
				System.out.println("SKIPPING");
			}
		}

		@Override
		public void end(State.Return state) {
			if(state.depth == 1) {
				out.add(new Trace.Returns(state.getReturnData()));
			}
		}

		@Override
		public void revert(State.Revert state) {
			if(state.depth == 1) {
				out.add(new Trace.Reverts(state.getReturnData()));
			}
		}

		@Override
		public void exception(State.Invalid state) {
			if(state.depth == 1) {
				out.add(new Trace.Exception(toErrorCode(state.getErrorCode())));
			}
		}

		@Override
		public void callContinue(CallContinue state) {
			// For now we do nothing.
		}
	}

	public static Trace.Exception.Error toErrorCode(EvmState_Compile.Error err) {
		if (err instanceof EvmState_Compile.Error_INSUFFICIENT__GAS) {
			return Trace.Exception.Error.INSUFFICIENT_GAS;
		} else if (err instanceof EvmState_Compile.Error_INVALID__OPCODE) {
			return Trace.Exception.Error.INVALID_OPCODE;
		} else if (err instanceof EvmState_Compile.Error_INVALID__JUMPDEST) {
			return Trace.Exception.Error.INVALID_JUMPDEST;
		} else if (err instanceof EvmState_Compile.Error_STACK__OVERFLOW) {
			return Trace.Exception.Error.STACK_OVERFLOW;
		} else if (err instanceof EvmState_Compile.Error_STACK__UNDERFLOW) {
			return Trace.Exception.Error.STACK_UNDERFLOW;
		} else if (err instanceof EvmState_Compile.Error_MEMORY__OVERFLOW) {
			return Trace.Exception.Error.MEMORY_OVERFLOW;
		} else if (err instanceof EvmState_Compile.Error_CALLDEPTH__EXCEEDED) {
			return Trace.Exception.Error.CALLDEPTH_EXCEEDED;
		} else {
			return Trace.Exception.Error.UNKNOWN;
		}
	}
}
