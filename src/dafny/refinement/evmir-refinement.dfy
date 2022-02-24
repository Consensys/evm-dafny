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

module EVMIRRefinement {

    import opened EVMSeq
    import opened EVMIR
    import opened EVM 
    import opened Helpers
   
    //  Warm up proof

    /**
     *  while(c, body)
     *  translates to:
     *  a1: jumpi(!c, end)
     *  a2: body  
     *  a3: jump a1
     *  end: 
     *
     */
    lemma singleLoop<S>(i: EVMInst, cond: S -> bool, n: nat, s: S)
        ensures runEVMIR([While(cond, i)], s, n) ==
            runEVM(
                1,
                map[
                    1 := Jumpi(negF(cond), 0),
                    2 := AInst(i),
                    3 := Jump(1)
                ], 
                s, 
                3 * n).0
    {
        //  For convenience and clarity, store program in a var 
        var p := map[
                        1 := Jumpi(negF(cond), 0),
                        2 := AInst(i),
                        3 := Jump(1)
                    ];
        if n == 0 {
            //  state should be the same
            assert runEVMIR([While(cond, i)], s, n) == s == runEVM(1, p, s, 3 * n).0;
        } else if cond(s) {
            //  verified calculations. Unfold one round of jump program
            calc == {
                runEVM(1, p, s, 3 * n);
                runEVM(1 + 1, p, s, 3 * n - 1);
                runEVM(2, p, s, 3 * n - 1);

                runEVM(3, p, runInst(i, s), 3 * n - 2 );
                runEVM(1, p, runInst(i, s), 3 * n - 3);
                //  after one iteration, n - 1 remaining from new state after body
                runEVM(1, p, runInst(i, s), 3 * (n - 1));
            }
            //  Because body of while and jump progs are the same, theh reach the same
            //  state after one iteration of the body.
            calc == {
                runEVMIR([While(cond, i)], s, n);
                runEVMIR([While(cond, i)], runInst(i, s) , n - 1);
            }
            //  And by induction, the n - 1 remaining steps compute the same
            //  result.
            singleLoop(i, cond, n - 1, runInst(i, s));
        } else {
            //  state should be the same too.
            assert !cond(s);
        }
    }

    /**
     *  IfElse refinement proof.
     */
    lemma singleIfElse<S>(i1: EVMInst, i2: EVMInst, cond: S -> bool, n: nat, k: nat, s: S)
        requires n >= 2 && k >= n + 3
        ensures runEVMIR([IfElse(cond, i1, i2)], s, n) ==
            runEVM(
                1,
                map[
                    1 := Jumpi(negF(cond), 4),
                    2 := AInst(i1),
                    3 := Jump(5),
                    4 := AInst(i2)
                ], 
                s, 
                k).0 
    {
        var p1 := [IfElse(cond, i1, i2)];
        var p2 := map[
                    1 := Jumpi(negF(cond), 4),
                    2 := AInst(i1),
                    3 := Jump(5),
                    4 := AInst(i2)
                ];
        
        if cond(s) {
            calc == {
                runEVMIR([IfElse(cond, i1, i2)], s, n);
                runEVMIR([IfElse(cond, i1, i2)][1..], runInst(i1, s), n - 1); 
                runEVMIR([], runInst(i1, s), n - 1); 
                runInst(i1, s);
            }
            calc == {
                runEVM(1, p2, s, k);
                { assert !negF(cond)(s); }
                runEVM(1 + 1 , p2, s, k - 1);
                runEVM(3, p2, runInst(i1, s), k - 2);
                runEVM(5, p2, runInst(i1, s), k - 1);
                (runInst(i1, s), 0);
            }
        } else {
            assert !cond(s);
            calc == {
                runEVMIR([IfElse(cond, i1, i2)], s, n);
                { assert !cond(s); }
                runEVMIR([IfElse(cond, i1, i2)][1..], runInst(i2, s), n - 1); 
                runEVMIR([], runInst(i2, s), n - 1); 
                runInst(i2, s);
            }
            calc == {
                runEVM(1, p2, s, k);
                { assert negF(cond)(s); }
                runEVM(4 , p2, s, k - 1);
                runEVM(5, p2, runInst(i2, s), k - 2);
                (runInst(i2, s), 0);
            }
        }
    }
    
}
