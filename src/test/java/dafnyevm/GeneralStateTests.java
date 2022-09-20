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
import evmtools.util.Bytecodes;
import evmtools.util.Hex;
import evmtools.core.Environment;
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
			"stMemoryTest/oog.json", // #299
			"stMemoryTest/stackLimitGas_1023.json", // #201
			"stMemoryTest/stackLimitGas_1024.json", // #201
			"stMemoryTest/stackLimitGas_1025.json", // #201
			"vmIOandFlowOperations/jumpToPush.json", // #241
			"stReturnDataTest/create_callprecompile_returndatasize.json", // #266
			"stReturnDataTest/modexp_modsize0_returndatasize.json", // #266
			"stRevertTest/RevertPrecompiledTouchExactOOG.json",  // #266
			"stRevertTest/RevertPrecompiledTouch.json",  // #266
			"stRevertTest/RevertPrecompiledTouch_nonce.json",  // #266
			"stRevertTest/RevertPrecompiledTouch_noncestorage.json",  // #266
			"stRevertTest/RevertPrecompiledTouch_storage.json",  // #266
			"stCreate2/create2callPrecompiles.json", // #266
			"stCreateTest/CREATE_HighNonce.json",// #318
			"stCreateTest/CREATE_FirstByte_loop.json", // #318
			"stCreate2/create2collisionCode.json", // #318
			"stCreate2/create2collisionCode2.json", // #318
			"stCreate2/create2collisionSelfdestructed2.json", // #318
			"stCreate2/create2collisionNonce.json", // #318
			"stCreate2/create2collisionSelfdestructedOOG.json",  // #318
			"stCreate2/create2collisionSelfdestructed.json", // #318
			"stCreate2/create2collisionSelfdestructedRevert.json", // #318
			"stCreate2/CREATE2_FirstByte_loop.json", // #318
			"stCreate2/CREATE2_HighNonce.json", // #318
			"stCreate2/CREATE2_EOF1.json", // #318
			"stCreate2/create2SmartInitCode.json", // #318
			"stCreate2/Create2OOGafterInitCodeRevert2.json", // #318
			"stCreate2/CREATE2_Bounds3.json", // # 319
			"stCreate2/CREATE2_Suicide.json", // #320
			"stExtCodeHash/callToSuicideThenExtcodehash.json", // #320
			"stExtCodeHash/extCodeHashCreatedAndDeletedAccountStaticCall.json", // #320
			// Unknowns
			"stCreateTest/CREATE_ContractRETURNBigOffset.json", // large return?
			"stCreateTest/CREATE_EContractCreateEContractInInit_Tr.json",
			"stCreateTest/CREATE_ContractSSTOREDuringInit.json", // wierd with CREATE?
			"stCreateTest/CREATE_EContractCreateNEContractInInit_Tr.json", // wierd with CREATE?
			"stCreateTest/CREATE_EOF1.json", // weird with CREATE?
			"stCreateTest/TransactionCollisionToEmptyButCode.json", // wierd?
			"stCreateTest/TransactionCollisionToEmptyButNonce.json", // wierd?
			"stCreate2/create2noCash.json", // Unknown exception
			// Gas Unknowns
			"stRevertTest/NashatyrevSuicideRevert.json", // Gas (Unknown)
			"stRevertTest/RevertRemoteSubCallStorageOOG.json", // Gas (Unknown)
			"stCreateTest/CREATE_AcreateB_BSuicide_BStore.json", // Gas (Unknown)
			"stCreateTest/CreateCollisionResults.json", // Gas (Unknown)
			"stCreateTest/CreateOOGafterInitCodeRevert2.json", // Gas (Unknown)
			"stCreate2/create2checkFieldsInInitcode.json", // Gas (Unknown)
			//
			"vmIOandFlowOperations/jump.json", // #295
			"vmIOandFlowOperations/jumpi.json", // #295
			"stRevertTest/RevertDepth2.json", // #295
			"stRevertTest/LoopDelegateCallsDepthThenRevert.json", // #295
			"stRevertTest/RevertDepthCreateAddressCollision.json", // #295
			"stMemoryTest/memCopySelf.json", // #295
			"stSelfBalance/selfBalanceCallTypes.json", // #295
			"stCallCodes/callcallcall_ABCB_RECURSIVE.json", // #295
			"stCallCodes/callcallcallcode_ABCB_RECURSIVE.json", // #295
			"stCallCodes/callcallcodecall_ABCB_RECURSIVE.json", // #295
			"stCallCodes/callcallcodecallcode_ABCB_RECURSIVE.json", // #295
			"stCallCodes/callcodecallcall_ABCB_RECURSIVE.json", // #295
			"stCallCodes/callcodecallcallcode_ABCB_RECURSIVE.json", // #295
			"stCallCodes/callcodecallcodecall_ABCB_RECURSIVE.json", // #295
			"stCallCodes/callcodecallcodecallcode_ABCB_RECURSIVE.json", // #295
			"stCreateTest/CREATE_EmptyContractAndCallIt_0wei.json", // #295
			"stCreateTest/CREATE_EmptyContractAndCallIt_1wei.json", // #295
			"stCreateTest/CREATE_EmptyContractWithStorageAndCallIt_0wei.json", // #295
			"stCreateTest/CREATE_EmptyContractWithStorageAndCallIt_1wei.json", // #295
			"stCreateTest/CREATE_EmptyContractWithStorage.json", // #295
			"stCreateTest/CREATE_EContractCreateNEContractInInitOOG_Tr.json", // #295
			"stCreateTest/CREATE_empty000CreateinInitCode_Transaction.json", // #295
			"stCreateTest/CreateCollisionToEmpty.json", // #295
			"stCreateTest/TransactionCollisionToEmpty.json", // #295
			"stCreate2/CREATE2_HighNonceDelegatecall.json", // #295
			"stRevertTest/LoopCallsDepthThenRevert2.json", // #295
			"stRevertTest/LoopCallsDepthThenRevert3.json", // #295
			"stRevertTest/LoopCallsDepthThenRevert.json", // #295
			"stExtCodeHash/extcodehashEmpty.json", // #295
			//
			"stSStoreTest/InitCollision.json", // #295
			"stSStoreTest/InitCollisionNonZeroNonce.json", // #295
			"stSStoreTest/sstore_0to0.json", // #295
			"stSStoreTest/sstore_0to0to0.json", // #295
			"stSStoreTest/sstore_0to0toX.json", // #295
			"stSStoreTest/sstore_0toX.json", // #295
			"stSStoreTest/sstore_0toXto0.json", // #295
			"stSStoreTest/sstore_0toXto0toX.json", // #295
			"stSStoreTest/sstore_0toXtoX.json", // #295
			"stSStoreTest/sstore_0toXtoY.json", // #295
			"stSStoreTest/SstoreCallToSelfSubRefundBelowZero.json", // #295
			"stSStoreTest/sstore_changeFromExternalCallInInitCode.json", // #295
			"stSStoreTest/sstoreGas.json", // #295
			"stSStoreTest/sstore_gasLeft.json", // #295
			"stSStoreTest/sstore_Xto0.json", // #295
			"stSStoreTest/sstore_Xto0to0.json", // #295
			"stSStoreTest/sstore_Xto0toX.json", // #295
			"stSStoreTest/sstore_Xto0toXto0.json", // #295
			"stSStoreTest/sstore_Xto0toY.json", // #295
			"stSStoreTest/sstore_XtoX.json", // #295
			"stSStoreTest/sstore_XtoXto0.json", // #295
			"stSStoreTest/sstore_XtoXtoX.json", // #295
			"stSStoreTest/sstore_XtoXtoY.json", // #295
			"stSStoreTest/sstore_XtoY.json", // #295
			"stSStoreTest/sstore_XtoYto0.json", // #295
			"stSStoreTest/sstore_XtoYtoX.json", // #295
			"stSStoreTest/sstore_XtoYtoY.json", // #295
			"stSStoreTest/sstore_XtoYtoZ.json", // #295
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
			// Construct environment
			DafnyEvm.BlockInfo env = buildEnvironment(instance.getEnvironment());
			// Construct EVM
			ArrayList<Trace.Element> elements = new ArrayList<>();
			StructuredTracer tracer = new StructuredTracer(elements);
			// FIXME: following contains a workaround for an issue with the trace output,
			// whereby traces are used the _block's gas limit_ rather than the
			// _transaction's gas limit_.  #245
			DafnyEvm evm = new DafnyEvm().tracer(tracer).gasPrice(tx.gasPrice).blockInfo(env).to(tx.to).sender(tx.sender)
					.origin(tx.sender).gas(env.gasLimit).value(tx.value).data(tx.data);
			// Configure world state
			configureWorldState(evm,tx,instance.getWorldState());
			// Run the call or create
			if(tx.to != null) {
				evm.call();
			} else {
				evm.create();
			}
			//
			Trace tr = new Trace(elements);
			// Finally check for equality.
			assertEquals(instance.getTrace(),tr);
		}
	}

	/**
	 * Construct the necessary block environment from the test's environmental
	 * parameters.
	 *
	 * @param env
	 * @return
	 */
	public DafnyEvm.BlockInfo buildEnvironment(Environment env) {
		DafnyEvm.BlockInfo info = new DafnyEvm.BlockInfo();
		info = info.coinBase(env.currentCoinbase);
		info = info.timeStamp(env.currentTimestamp);
		// NOTE: following is commented out whilst trace data is generated using the
		// "evm" tool directly, as this does not allow a block number other than zero.
		//info = info.number(env.currentNumber);
		info = info.number(0);
		info = info.difficulty(env.currentDifficulty);
		info = info.gasLimit(env.currentGasLimit);
		return info;
	}

	/**
	 * Apply
	 * @param st
	 * @param evm
	 * @return
	 */
	public void configureWorldState(DafnyEvm evm, Transaction tx, WorldState ws) {
		// Initialise world statew
		for(Map.Entry<BigInteger, evmtools.core.Account> e : ws.entrySet()) {
			evmtools.core.Account acct = e.getValue();
			evm.create(e.getKey(), acct.nonce, acct.balance, acct.storage, acct.code);
		}
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
			int depth = state.getDepth();
//			long gas = state.getRemainingGas().longValueExact();
			long gas = 0; // for now
			// NOTE: to make traces equivalent with Geth we cannot appear to have "executed"
			// the invalid bytecode.
			if(op != Bytecodes.INVALID) {
				byte[] memory = state.getMemory();
				BigInteger[] stack = (BigInteger[]) state.getStack();
				// FIXME: this is a hack until such time as Geth actually reports storage.
				//Map<BigInteger, BigInteger> storage = state.getStorage();
				Map<BigInteger, BigInteger> storage = new HashMap<>();
				out.add(new Trace.Step(pc, op, depth, gas, stack, memory, storage));
			} else {
				System.out.println("SKIPPING");
			}
		}

		@Override
		public void end(State.Return state) {
			if(state.depth == 1) {
				// Unfortunately, Geth only reports RETURNS on the outermost contract call.
				out.add(new Trace.Returns(state.getReturnData()));
			}
		}

		@Override
		public void revert(State.Revert state) {
			if(state.depth == 1) {
				// Unfortunately, Geth only reports REVERTS on the outermost contract call.
				out.add(new Trace.Reverts(state.getReturnData()));
			}
		}

		@Override
		public void exception(State.Invalid state) {
			out.add(new Trace.Exception(toErrorCode(state.getErrorCode())));
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
		} else if (err instanceof EvmState_Compile.Error_RETURNDATA__OVERFLOW) {
			return Trace.Exception.Error.RETURNDATA_OVERFLOW;
		} else {
			return Trace.Exception.Error.UNKNOWN;
		}
	}
}
