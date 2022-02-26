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

    /** Programs with block of instructions, while loops/ifs. */
    datatype EVMIRProg<!S> =  
        |   Block(i:EVMInst)
        |   While(cond: S -> bool, body: EVMIRProg)
        |   IfElse(cond: S -> bool, ifBody: EVMIRProg, elseBody: EVMIRProg) 

    /**
     *  Run n steps of the program.
     *  Interpretation of a subset of EVM-IR.
     *
     *  @param  p   A program.
     *  @param  s   A state.
     *  @param  n   The number of steps to execute.
     *  @returns    The state obtained after executing `n` steps of `p`. 
     */
    function method runEVMIR<S>(p: seq<EVMIRProg>, s: S, n: nat): S 
        decreases n - 1
    {   
        if n == 0 || p == [] then s 
            //  max number of steps reached or program has terminated. 
        else 
            match p[0] 
                case Block(i) => runInst(i, s)
                case While(c, Block(b)) => 
                    if c(s) then runEVMIR(p, runInst(b, s), n - 1)
                    else runEVMIR(p[1..], s , n - 1)
                case While(c, b) => s   // Todo
                case IfElse(c, Block(b1), Block(b2)) => 
                    if c(s) then runEVMIR(p[1..], runInst(b1, s), n - 1)
                    else  runEVMIR(p[1..], runInst(b2, s), n - 1)
                 case IfElse(c, _, _) =>  s   // Todo
    }

    /**
     *  Interpretation of EVM-IR.
     *
     *  @note   In this interoretation a test fopr a condition costs 1.
     */
    function method runEVMIR2<S>(p: seq<EVMIRProg>, s: S, n: nat): (S, nat) 
        ensures runEVMIR2(p, s, n).1 <= n 
        ensures n > 0 && p != [] ==> runEVMIR2(p, s, n).1 < n
        decreases n - 1
    {   
        if n == 0 || p == [] then (s, n) 
            //  max number of steps reached or program has terminated. 
        else 
            match p[0] 
                case Block(i) => (runInst(i, s), n - 1)
                case While(c, b) => 
                    if c(s) then 
                        var (s', n') := runEVMIR2([b], s, n - 1);
                        runEVMIR2(p, s', n - 1 - n')
                    else runEVMIR2(p[1..], s , n - 1)
                case IfElse(c, b1, b2) => 
                    var (s', n') := if c(s) then runEVMIR2([b1], s, n - 1) else runEVMIR2([b2], s, n - 1);
                    runEVMIR2(p[1..], s', n - 1 - n')
    }
}
