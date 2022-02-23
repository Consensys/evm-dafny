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
 
include "evm-seq.dfy"

/**
 *  Provides EVM intermediate representation with structured
 *  EVM programs (loops and no jumps).
 */
module EVMIR {

    import opened EVMSeq

    /** Programs with while loops/ifs. */
    datatype EVMIR<!S> = 
        |   While(cond: S -> bool, body: EVMInst)
        |   IfElse(cond: S -> bool, ifBody: EVMInst, elseBody: EVMInst)

    /**
     *  Run n steps of the program.
     *  @param  p   A program.
     *  @param  s   A state.
     *  @param  n   The number of steps to execute.
     *  @returns    The state obtained after executing `n` steps of `p`. 
     */
    function method runEVMIR<S>(p: seq<EVMIR>, s: S, n: nat): S 
        decreases n - 1
    {   
        if n == 0 || p == [] then s 
            //  max number of steps reached or program has terminated. 
        else 
            match p[0] 
                case While(c, b) => 
                    if c(s) then runEVMIR(p, runInst(b, s), n - 1)
                    else runEVMIR(p[1..], s , n - 1)
                case IfElse(c, b1, b2) => 
                    if c(s) then runEVMIR(p, runInst(b1, s), n - 1)
                    else  runEVMIR(p, runInst(b2, s), n - 1)
    }
}
