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

include "./evm-seq.dfy"
include "./evmir.dfy"
include "./evm.dfy"
include "../utils/Helpers.dfy"

/**
 *  Provides proofs that EVM code simulates some corresponding EVMIR code.
 */
module EVMIRSimulation {

    import opened EVMSeq
    import opened EVMIR
    import opened EVM 
    import opened Helpers
   
    //  Warm up proofs

    /**
     *  Block of instructions. Simulation proof.
     *
     *  @returns    The (minimum) number of steps in the EVMIR to simulate n steps in EVM. 
     */
    lemma singleBlockSim<S>(i: EVMInst, cond: S -> bool, n: nat, s: S) returns (k: nat)
        ensures k <= n && runEVMIR([Block(i)], s, k) ==
            runEVM(
                1,
                map[
                    1 := AInst(i)
                ], 
                s, 
                n).0
    {
        k := n;
    }

    /**
     *  If Then Else Simulation proof.
     *
     *  @returns    The (minimum) number of steps in the EVMIR to simulate n steps in EVM. 
     */
    lemma ifTheElseSim<S>(i1: EVMInst, i2: EVMInst, cond: S -> bool, n: nat, s: S) returns (k: nat)
        // requires n > 2
        ensures k <= n && runEVMIR([IfElse(cond, i1, i2)], s, k) ==  
            runEVM(
                1,
                map[
                    1 := Jumpi(negF(cond), 4),
                    2 := AInst(i1),
                    3 := Jump(5),
                    4 := AInst(i2)
                ], 
                s, 
                n).0
    { 
        var p := map[
                    1 := Jumpi(negF(cond), 4),
                    2 := AInst(i1),
                    3 := Jump(5),
                    4 := AInst(i2)
                ];
        if n < 3 {
            //  if less than 1 step, only evaluate condition which takes no steps in EVM-IR
            if n <= 1 {
                k := 0 ;
            } else {
                //  Evaluate condition and execute i1 or i2. One step in EVM-IR
                k := 1;
            }
        } else {
            if cond(s) {
                //  Execute the ifBody
                calc == {
                    runEVM(1, p, s, n);
                    runEVM(2, p, s, n - 1);
                    runEVM(3, p, runInst(i1, s), n - 2);
                    runEVM(5, p, runInst(i1, s), n - 3);
                }
                //  EVM-IR program simulates p in 2 steps
                calc == {
                    runEVMIR([IfElse(cond, i1, i2)], s, n);
                    runEVMIR([], runInst(i1, s), n - 1);
                    runInst(i1, s);
                }
                k := n - 2;
            } else {
                assert !cond(s);
                calc == {
                    runEVM(1, p, s, n);
                    runEVM(4, p, s, n - 1);
                    runEVM(5, p, runInst(i2, s), n - 2);
                }
                //  EVM-IR program simulates p in 2 steps
                calc == {
                    runEVMIR([IfElse(cond, i1, i2)], s, n);
                    runEVMIR([], runInst(i2, s), n - 1);
                    runInst(i2, s);
                }
                k := n - 2;
            }
        }
    }

    /**
     *  Single While loop.
     *
     *  @returns    The (minimum) number of steps in the EVMIR to simulate n steps in EVM. 
     */
    lemma singleWhileSim<S>(i: EVMInst, cond: S -> bool, n: nat, s: S) returns (k: nat)
         ensures k <= n && runEVMIR([While(cond, Block(i))], s, k) ==
            runEVM(
                1,
                map[
                    1 := Jumpi(negF(cond), 4),
                    2 := AInst(i),
                    3 := Jump(1)
                ], 
                s, 
                n).0
    {
        //  For convenience and clarity, store program in a var 
        var p := map[
                    1 := Jumpi(negF(cond), 4),
                    2 := AInst(i),
                    3 := Jump(1)
                ];
        if n < 2 {
            //  Only one step can be simulated so the instruction at pc is not executed.
            k := 0;
        } else if n < 3 {
            //  Exactly two steps in the EVM. 
            assert n == 2;
            if cond(s) {
                k := 1;
            } else {
                assert !cond(s);
                k := 0;
            }
        } else {
            //  More than 2 steps in the EVM. So at least one iteration of the EVM body.
            assert n > 2;
            if cond(s) {
                calc == {
                    runEVM(1, p, s, n);
                    runEVM(2, p, s, n - 1);
                    runEVM(3, p, runInst(i, s), n - 2);
                    runEVM(1, p, runInst(i, s), n - 3);
                }
                //  Because body of while and jump progs are the same, they reach the same
                //  state after one iteration of the body.
                calc == {
                    runEVMIR([While(cond, Block(i))], s, n);
                    runEVMIR([While(cond, Block(i))], runInst(i, s), n - 1);
                }
                //  And by induction, we can get a simulation for the n - 3 remaining steps compute the same
                //  result.
                var xk := singleWhileSim(i, cond, n - 3, runInst(i, s));
                //  Overall we do the body of the loop once and then in xk steps simulate the rest.
                k := 1 + xk;
            } else {
                //  Exit the loop.
                assert !cond(s);
                k := 1;
            }    
        }
    }    
}
