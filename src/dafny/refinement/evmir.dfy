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
include "../utils/Graphs.dfy"

/**
 *  Provides EVM intermediate representation with structured
 *  EVM programs (loops and no jumps).
 */
module EVMIR {

    import opened EVMSeq
    import opened Graphs

    /** Programs with block of instructions, while loops/ifs. */
    datatype EVMIRProg<!S> =  
        |   Block(i:EVMInst)
        // |   Sequence(p1: EVMIRProg, p2: EVMIRProg)
        |   While(cond: S -> bool, body: seq<EVMIRProg>)
        |   IfElse(cond: S -> bool, ifBody: seq<EVMIRProg>, elseBody: seq<EVMIRProg>) 
        // |   Skip()

    datatype EVMIRProg2<!S> =  
        |   Block(i:EVMInst)

        // |   Sequence(p1: EVMIRProg, p2: EVMIRProg)
        |   While(cond:  bool, body: seq<EVMIRProg2>)
        |   IfElse(cond: bool, ifBody: seq<EVMIRProg2>, elseBody: seq<EVMIRProg2>) 
        // |   Skip()
    
    /** A DiGraph with nat number vertices. */
    datatype CFG<!S(==)> = CFG(entry: S, g: LabDiGraph<S>, exit: S) 

    /**
     *  Print a CFG of type `S`.
     *  @param  g   A control flow graph.
     *  @param  f   A converter from `S` to a printable string.
     */
    method printCFG(cfg: CFG<nat>, name: string := "noName") 
        requires |cfg.g| >= 1
    {
        diGraphToDOT(cfg.g, cfg.exit + 1, name);  
    }

    /**
     *  Semantics of EVMIR programs.
     *
     *  @param  p   An EVMIR program.
     *  @param  s   A state.
     *  @returns    The state obtained after executing one step of `p` from `s`,
     *              and the program that is left to be executed.
     */
    function method stepEVMIR<S>(p: seq<EVMIRProg>, s: S): (S, seq<EVMIRProg>) 
    {   
        if |p| == 0 then (s, [])
        else 
            match p[0]
                case Block(i) => (runInst(i, s), p[1..])
                
                case While(c, b) => 
                        if c(s) then
                            var (s', p') := stepEVMIR(b, s);
                            (s', p' + p)
                        else 
                            (s, p[1..])
                case IfElse(c, b1, b2) => 
                    if c(s) then 
                        var (s', p') := stepEVMIR(b1, s);
                        (s', p' + p[1..])
                    else var (s', p') := stepEVMIR(b2, s);
                        (s', p' + p[1..])
    }

    /**
     *  
     *  @param  k   First number available to id new state.
     */
    function method toCFG(inCFG: CFG<nat>, p: seq<EVMIRProg2>, k: nat): (CFG<nat>, nat)
        // decreases p, s - {p}
        decreases p 
    {
        if p == [] then (inCFG, k)
        else 
            match p[0]
                case Block(i) => 
                    //  Build CFG of Block, append to previous graph, and then append graph of tail(p)
                    toCFG(
                        CFG(inCFG.entry, inCFG.g + [(k, k + 1, i.name)], k + 1),
                        p[1..],
                        k + 1
                    )
                
                case IfElse(c, b1, b2) => 
                    //  Add true and false edges to current graph
                    //  Build cfgThen starting numbering from k + 1
                    var (cfgThen, indexThen) := toCFG(inCFG, b1, k + 1);
                    //  Build cfgElse starting numbering from indexThen + 1
                    var (cfgThenElse, indexThenElse) := toCFG(cfgThen, b2, indexThen + 1);
                    //  Build IfThenElse cfg stitching together previous cfgs and 
                    //  wiring cfgThen.exit to cfgElse.exit with a skip instruction
                    var cfgIfThenElse := CFG(
                                            cfgThenElse.entry, 
                                            cfgThenElse.g + 
                                                [(inCFG.exit, k + 1, "TRUE/IF")] +
                                                [(inCFG.exit, indexThen + 1, "FALSE/IF")] +
                                                [(cfgThen.exit, cfgThenElse.exit, "skip")],
                                            cfgThenElse.exit
                                        );
                    toCFG(cfgIfThenElse, p[1..], indexThenElse)

                case While(c, b) => 
                    //  Build CFG for b from k + 1 when while condition is true 
                    var tmpCFG := CFG(inCFG.entry, inCFG.g + [(k, k + 1, "TRUE/WHILE")], k + 1);
                    //  
                    var (whileBodyCFG, indexBodyExit) := toCFG(tmpCFG, b, k + 1);
                    var cfgWhile := CFG(
                                        whileBodyCFG.entry, 
                                        whileBodyCFG.g + 
                                            // [(whileBodyCFG.exit, k + 1, "TRUE")] +
                                            //  Add edge for while condition false
                                            [(inCFG.exit, indexBodyExit + 1, "FALSE/WHILE")] +
                                            [(whileBodyCFG.exit, k, "loop")],
                                        indexBodyExit + 1
                                        );
                    toCFG(cfgWhile, p[1..], indexBodyExit + 1)
    }
        
    /**
     *  Run n steps of the program.
     *  Interpretation of a subset of EVM-IR.
     *
     *  @param  p   A program.
     *  @param  s   A state.
     *  @param  n   The number of steps to execute.
     *  @returns    The state obtained after executing `n` steps of `p`. 
     */
    // function method runEVMIR<S>(p: seq<EVMIRProg>, s: S, n: nat): S 
    //     decreases n - 1
    // {   
    //     if n == 0 || p == [] then s 
    //         //  max number of steps reached or program has terminated. 
    //     else 
    //         match p[0] 
    //             case Block(i) => runInst(i, s)
    //             case While(c, Block(b)) => 
    //                 if c(s) then runEVMIR(p, runInst(b, s), n - 1)
    //                 else runEVMIR(p[1..], s , n - 1)
    //             case While(c, b) => s   // Todo
    //             case IfElse(c, Block(b1), Block(b2)) => 
    //                 if c(s) then runEVMIR(p[1..], runInst(b1, s), n - 1)
    //                 else  runEVMIR(p[1..], runInst(b2, s), n - 1)
    //              case IfElse(c, _, _) =>  s   // Todo
    // }

    /**
     *  Interpretation of EVM-IR.
     *
     *  @param  p   An EVMIR program.
     *  @param  s   An initial step.
     *  @param  n   The maximum number of steps to execute.
     *  @returns    The state reached after running from `p` from `s` and the number
     *              (if any) of steps unused.
     *
     *  @note       In this interpretation a test for a condition costs 1.
     */
    // function method runEVMIR2<S>(p: seq<EVMIRProg>, s: S, n: nat): (S, nat) 
    //     ensures runEVMIR2(p, s, n).1 <= n 
    //     ensures n > 0 && p != [] ==> runEVMIR2(p, s, n).1 < n
    //     decreases n - 1
    // {   
    //     if n == 0 || p == [] then (s, n) 
    //         //  max number of steps reached or program has terminated. 
    //     else 
    //         match p[0] 
    //             case Block(i) => (runInst(i, s), n - 1)
    //             case While(c, b) => 
    //                 if c(s) then 
    //                     var (s', n') := runEVMIR2([b], s, n - 1);
    //                     runEVMIR2(p, s', n - 1 - n')
    //                 else runEVMIR2(p[1..], s , n - 1)
    //             case IfElse(c, b1, b2) => 
    //                 var (s', n') := if c(s) then runEVMIR2([b1], s, n - 1) else runEVMIR2([b2], s, n - 1);
    //                 runEVMIR2(p[1..], s', n - 1 - n')
    // }

    // function method runEVMIR3<S>(p: EVMIRProg, s: S, n: nat): (S, nat) 
    //     ensures runEVMIR3(p, s, n).1 <= n 
    //     // ensures n > 0 && p != [] ==> runEVMIR2(p, s, n).1 < n
    //     decreases n - 1
    // {   
    //     if n == 0 then (s, n) 
    //         //  max number of steps reached or program has terminated. 
    //     else 
    //         match p
    //             case Block(i) => (runInst(i, s), n - 1)
    //             case While(c, b) => 
    //                 if c(s) then 
    //                     var (s', n') := runEVMIR3(b, s, n - 1);
    //                     runEVMIR3(p, s', n - 1 - n')
    //                 else (s , n - 1)
    //             case IfElse(c, b1, b2) => 
    //                 if c(s) then runEVMIR3(b1, s, n - 1) else runEVMIR3(b2, s, n - 1)
    // }
}
