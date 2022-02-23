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

include "./evmir-types.dfy"
include "./evmir-semantics.dfy"

module EVMIRRefinement {

    import opened EVMIRTypes
    import opened EVMIRSemantics
   
    /**
     *  Translation proof.
     *  Assume two programs, a loop 
     *
     *  while(c, b)
     *  jumpi(!c, [b, jump[]])
     *
     */
    lemma foo202<S>(i: EVMInst, cond: S -> bool, n: nat, s: S)
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
        if n == 0 {
            //  
        } else if cond(s) {
            var p := map[
                        1 := Jumpi(negF(cond), 0),
                        2 := AInst(i),
                        3 := Jump(1)
                    ];

            calc == {
                runEVM(1, p, s, 3 * n);
                { assert 1 in p; assert !negF(cond)(s); }
                runEVM(1 + 1, p, s, 3 * n - 1);
                runEVM(2, p, s, 3 * n - 1);

                runEVM(3, p, runInst(i, s), 3 * n - 2 );
                runEVM(1, p, runInst(i, s), 3 * n - 3);
                runEVM(1, p, runInst(i, s), 3 * (n - 1));
            }
            calc == {
                runEVMIR([While(cond, i)], s, n);
                runEVMIR([While(cond, i)], runInst(i, s) , n - 1);
            }
            foo202(i, cond, n - 1, runInst(i, s));
        } else {
            assert !cond(s);
        }
    }
    
}
