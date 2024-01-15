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
import static org.junit.jupiter.api.Assertions.assertArrayEquals;
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
import java.util.Objects;
import java.util.stream.Stream;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.Triple;
import org.json.JSONException;
import org.json.JSONObject;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import dafnyevm.DafnyEvm.State;
import dafnyevm.util.StateTests;
import evmtools.core.LegacyTransaction;
import evmtools.core.Trace;
import evmtools.core.TraceTest;
import evmtools.core.Transaction;

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
    public final static String[] FORKS = {"Berlin","London","Shanghai"};
    /**
     * The directory containing the test files.
     */
    public final static Path TESTS_DIR = Path.of("tests");

    /**
     * Determine the maximum number of stack items that will be recorded in each
     * step.
     */
    private final static int STACK_LIMIT = 10;

    /**
     * The set of tests which are considered "impossible" by the execution specs
     * and, therefore, can be safely ignored.
     */
    public final static List<String> IMPOSSIBLES = Arrays.asList( //
            "stSStoreTest/InitCollision.json",
            "stRevertTest/RevertInCreateInInit.json",
            "stCreate2/RevertInCreateInInitCreate2.json");

    /**
     * Identifies test instances which (for various reasons) should be ignored. For
     * example, because the test does not currently pass. Each line in the list is a
     * regular expression matching against the test instance name. Each line must be
     * given a reason for this (i.e. an issue number) where possible.
     */
    public final static List<String> IGNORED_INSTANCES = Arrays.asList( //
            // #241
            "jump_.*_0_9_0",
            "jumpi_.*_0_14_0",
            "jumpToPush_.*_[0-9_]*",
            // #339
            "static_CallEcrecover0_0input_.*_0_8_0",
            "StaticcallToPrecompileFromContractInitialization_.*_0_0_0",
            "StaticcallToPrecompileFromCalledContract_.*_0_0_0",
            "StaticcallToPrecompileFromTransaction_.*_0_0_0",
            "precompsEIP2929_.*_0_(43|61|151|169|241|295)_0",
            "idPrecomps_.*_0_7_0",
            "ecpairing.*",
            "pairingTest.*",
            // #455
            "modexp_.*_[0123]_2_0", // int overflow
            // #531
            "CREATE_ContractRETURNBigOffset_.*_0_(0|1|2|3)_0",
            "codesizeOOGInvalidSize_.*_0_(0|1)_0",
            "randomStatetest643_.*_0_0_0",
            "randomStatetest384_.*_0_0_0",
            // #532
            "multiOwnedConstructionNotEnoughGasPartial_.*_0_0_0",
            "multiOwnedConstructionNotEnoughGas_.*_0_0_0",
            "walletConstructionOOG_.*_0_0_0",
            "dayLimitConstructionOOG_.*_0_0_0",
            // Performance
            "exp_.*_0_(1|2|9)_0",
            "expPower256Of256_.*_0_0_0",
            "randomStatetest(52|64|320|354|367|650)_.*_0_0_0",
            "gasCostExp_.*_0_8_0",
            "modexp_modsize0_returndatasize_.*_0_4_0",
            // #622
            "CreateAddressWarmAfterFail_.*",
            // #623
            "CreateOOGFromEOARefunds.*",
            // #624
            "CreateTransactionHighNonce.*",
            // #625
            "ecrecoverWeirdV.*",
            "ecrecoverShortBuff.*",
            "CallEcrecover_Overflow.*",
            // Unknowns
            "undefinedOpcodeFirstByte_.*_0_0_0",
            "InitCollisionNonZeroNonce_.*_[0-9_]*",
            "randomStatetest353_.*_0_0_0",
            "eip1559_.*_0_0_0",
            "badOpcodes_Berlin_0_23_0", // weird?
            // Shanghai Issues
            "badOpcodes_Shanghai_0_34_0",
            "coinbaseWarm.*_Shanghai.*",           
            "opcEFDiffPlaces_Shanghai.*",    
            "PythonRevertTest.*_Shanghai.*",
            "randomStatetest(26|30|45|199|207|244|246|295|307|508|646|571|577|628)_Shanghai_0_0_0",
            "TestContractSuicide_Shanghai_.*",
            "dummy");

    @ParameterizedTest
    @MethodSource("allTestFiles")
    public void tests(Triple<Path, String, TraceTest.Instance> tuple) throws IOException, JSONException {
    	final String fork = tuple.getMiddle();
        final TraceTest.Instance instance = tuple.getRight();
        //
        if (isIgnoredInstance(instance)) {
            // Force test to be ignored.
            assumeTrue(false);
        } else {
            TraceTest.Tx tx = instance.getTransaction();
            // Construct environment
            DafnyEvm.BlockInfo env = StateTests.toBlockInfo(instance.getEnvironment());
            // Construct EVM
            StructuredTracer tracer = new StructuredTracer();
            DafnyEvm evm = new DafnyEvm().tracer(tracer).blockInfo(env).fork(fork);
            // Configure world state
            StateTests.configureWorldState(evm, instance.getWorldState());
            // Run the call or create
            DafnyEvm.State<?> outcome = evm.execute((LegacyTransaction) tx.getTransaction());
            Trace actual = tracer.toTrace();
            Trace expected = tx.getTrace();
            //
            if (!Objects.equals(expected,actual)) {
                // NOTE: the following is really just to help provide additional debugging
                // support when running tests from e.g. gradle on the command line.
                System.err.println(tuple + " ==> " + outcome);
                printTraceDiff(expected, actual);
            }
            // Finally check for equality.
            assertEquals(expected, actual);
            // Check outcome matches
            if (tx.getOutcome() == Transaction.Outcome.UNKNOWN && outcome.getOutcome() != Transaction.Outcome.RETURN) {
                // NOTE: we ignore the case here where the expected outcome is an unknown error,
                // and we have an error being reported. This is just a workaround for Geth
                // which, in some cases, does not provide accurate error reporting for reasons
                // unknown.
            } else {
                assertEquals(tx.getOutcome(), outcome.getOutcome());
            }
            // Sanity check return data matches as well
            assertArrayEquals(tx.getData(),outcome.getReturnData());
        }
    }

    /**
     * Attempt to identify where the traces diverge.
     *
     * @param expected
     * @param actual
     */
    private static void printTraceDiff(Trace traceExpected, Trace traceActual) {
        if(traceExpected == null || traceActual == null) {
            System.err.println("(expected) " + traceExpected);
            System.err.println("(actual)   " + traceActual);
        } else {
            List<Trace.Element> expected = traceExpected.getElements();
            List<Trace.Element> actual = traceActual.getElements();
            //
            int n = Math.min(expected.size(), actual.size());
            for (int i = 0; i != n; ++i) {
                Trace.Element eith = expected.get(i);
                Trace.Element aith = actual.get(i);
                // FIXME: handle nested traces here
                if (!eith.equals(aith)) {
                    System.err.println("(expected) " + eith);
                    System.err.println("(actual)   " + aith);
                    System.err.println("--");
                    return;
                }
            }
        }
    }

    // Here we enumerate all available test cases.
    private static Stream<Triple<Path, String, TraceTest.Instance>> allTestFiles() throws IOException {
        return readTestFiles(TESTS_DIR);
    }

    /**
     * Determine whether a particular test instance should be (for some reason) ignored.
     * @param instance
     * @return
     */
    private static boolean isIgnoredInstance(TraceTest.Instance instance) {
        String name = instance.toString();
        for (int i = 0; i != IGNORED_INSTANCES.size(); ++i) {
            String regex = IGNORED_INSTANCES.get(i);
            if(name.matches(regex)) {
                return true;
            }
        }
        return false;
    }

    private static boolean isImpossible(Path path) {
        // Normalise path notation for platofmr
        String p = path.toString().replace(File.separator, "/");
        // Check whether this matches an IGNORE or not.
        for (int i = 0; i != IMPOSSIBLES.size(); ++i) {
            String ith = IMPOSSIBLES.get(i);
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

    public static Stream<Triple<Path, String, TraceTest.Instance>> readTestFiles(Path dir) throws IOException {
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
    private static Stream<Triple<Path, String, TraceTest.Instance>> streamTestsFromFiles(Stream<Path> files) {
        return files.flatMap(f -> {
            try {
                return streamTestsFromFile(f);
            } catch (Throwable e) {
                System.out.println("*** Error reading file \"" + f + "\" (" + e.getMessage() + ")");
                e.printStackTrace();
                return null;
            }
        });
    }

    private static Stream<Triple<Path, String, TraceTest.Instance>> streamTestsFromFile(Path f) throws IOException, JSONException {
    	ArrayList<Triple<Path, String, TraceTest.Instance>> instances = new ArrayList<>();
        if (!isImpossible(f)) {
            // Read contents of fixture file
            String contents = Files.readString(f);
            // Convert fixture into JSON
            JSONObject json = new JSONObject(contents);
            // Parse into one or more tests
            for (String test : JSONObject.getNames(json)) {
                TraceTest tt = TraceTest.fromJSON(test, json.getJSONObject(test));
                for (String fork : FORKS) {
                	if (tt.hasInstances(fork)) {
                		// Add all instances
                		for (TraceTest.Instance i : tt.getInstances(fork)) {
                			instances.add(Triple.of(f, fork, i));
                		}
                	}
                }
            }
        }
        return instances.stream();
    }

    public static class StructuredTracer extends DafnyEvm.TraceAdaptor {
        /**
         * Defines the maximum number of stack elements to store with each step. This
         * needs to agree with the number used to generate the trace files, otherwise
         * things will fail.
         */
        private final ArrayList<List<Trace.Element>> stack;
        /**
         * The final trace ready for reading.
         */
        private Trace trace;

        public StructuredTracer() {
            this.stack = new ArrayList<>();
        }

        public Trace toTrace() {
            return trace;
        }

        @Override
        public void enter() {
            this.stack.add(new ArrayList<>());
        }

        @Override
        public void step(DafnyEvm.State.Executing state) {
            int pc = state.getPC().intValueExact();
            int op = state.getOpcode();
            int depth = state.getDepth();
            long gas = state.getGas().longValueExact();
            byte[] memory = state.getMemory();
            BigInteger[] stack = (BigInteger[]) state.getStack();
            // FIXME: this is a hack until such time as Geth actually reports storage.
            // Map<BigInteger, BigInteger> storage = state.getStorage();
            Map<BigInteger, BigInteger> storage = new HashMap<>();
            // Trim the stack
            BigInteger[] trimmed = evmtools.util.Arrays.trimFront(STACK_LIMIT, stack);
            //
            add(new Trace.Step(pc, op, depth, gas, stack.length, trimmed, memory, storage));
        }

        @Override
        public void end(State.Return state) {
            done(Transaction.Outcome.RETURN,state.getReturnData());
        }

        @Override
        public void exception(State.Exception state) {
            done(state.getOutcome(),state.getReturnData());
        }

        private void add(Trace.Element element) {
            int last = stack.size() - 1;
            stack.get(last).add(element);
        }

        private void done(Transaction.Outcome outcome, byte[] data) {
            int last = stack.size() - 1;
            List<Trace.Element> elements = stack.get(last);
            stack.remove(last);
            // This mirrors Geth, which makes it hard to e.g. identify a revert when no code
            // was executed.
            Trace t = new Trace(elements, outcome, data);
            if (stack.size() == 0) {
                trace = t;
                stack.clear(); // for sanity checking
            } else if (stack.size() > 0 && elements.size() > 0) {
                add(new Trace.SubTrace(t));
            }
        }
    }
}
