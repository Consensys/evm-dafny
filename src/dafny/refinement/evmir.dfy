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
 *  Provide EVM intermediate representation with structured
 *  EVM programs (loops, if-then-else but no jumps).
 */
module EVMIR {

    import opened EVMSeq 
    import opened Graphs

    /** Programs with block of instructions, while loops/ifs. */
    datatype EVMIRProg<!S> =  
        |   Block(i:EVMInst)
        |   While(cond: S -> bool, body: seq<EVMIRProg>)
        |   IfElse(cond: S -> bool, ifBody: seq<EVMIRProg>, elseBody: seq<EVMIRProg>) 
    
    /** A labelled DiGraph with nat number vertices. */
    datatype CFG<!S(==)> = CFG(entry: nat, g: LabDiGraph<S>, exit: nat) 

    /**
     *  Print a CFG of type `S`.
     *  @param  g   A control flow graph.
     *  @param  f   A converter from `S` to a printable string.
     */
    method printCFG<S>(cfg: CFG<S>, name: string, m: map<nat, seq<EVMIRProg<S>>>) 
    {
        diGraphToDOT<S>(cfg.g, cfg.exit + 1, name, toTooltip(m, cfg.exit));   
    }

    /**
     *  Generate tooltip, node -> pretty printed EVMIRProg<nat>
     *  
     *  @param  m   A map from nodes to EVMIR code.
     *  @param  n   The number of nodes, should be the keys in the map too.
     *  @returns    The map m where every EVMIR code is pretty-printed.
     */
    function method toTooltip(m: map<nat, seq<EVMIRProg>>, n: nat): map<nat, string> 
    {
        if n == 0 && n in m then map[n := prettyEVMIR(m[n])] 
        else if n == 0 then map[n := "default"]
        else map[n := if n in m then prettyEVMIR(m[n]) else "default"]  + toTooltip(m, n - 1)
    }

    /**
     *  Print map for a CFG of type `S`.
     *  @param  g   A control flow graph.
     *  @param  f   A converter from `S` to a printable string.
     */
    method {:verify false} printCFGmap(m: map<nat, seq<EVMIRProg>>, name: string := "noName") 
        {
            for i := 0 to |m|
            {
                print "sim[", i, "] -> ";
                if i in m {
                    print prettyEVMIR(m[i]);
                } else {
                    print "Key not found:", i;
                }
                
                print "\n";
            }
        print "\n";
    }

    /**
     *  Generate a string with `k` spaces.
     *
        @param  k   The number of white spaces to generate. 
     */
    function method {:tailrecursion true} whiteSpaces(k: nat): string
    {
        if k == 0 then ""
        else " " + whiteSpaces(k - 1)
    }

    /**
     *  Generate a pretty-printed (string) EVMIR program.
     *  @param  p       The program to pretty-print.
     *  @param  k       The current indentation.
     *  @param  name    The name of the program.
     *  @returns        A string with the pretty-printed program `p`.
     */
    function method {:verify true} prettyEVMIR<S>(p: seq<EVMIRProg<S>>, k: nat := 0, name: string := "noName", tabSize: nat := 2): string
        decreases p
    {
        if p == [] then ""
        else 
            (match p[0]
                case Block(i) => whiteSpaces(k * tabSize) + i.name + "\n"
                case IfElse(c, b1, b2) => 
                    whiteSpaces(k * tabSize)+ "If (*) then\n" +
                    prettyEVMIR(b1, k + 1) +
                    whiteSpaces(k * tabSize) + "else\n" +
                    prettyEVMIR(b2, k + 1)
                case While(c, b) => 
                    whiteSpaces(k * tabSize) + "While (*) do\n" +
                    prettyEVMIR(b, k + 1) +
                    whiteSpaces(k * tabSize) + "od /* while */\n"
            ) + prettyEVMIR(p[1..], k)
    }

    /**
     *  Semantics of EVMIR programs.
     *
     *  @param  p   An EVMIR program.
     *  @param  s   A state.
     *  @returns    The state obtained after executing one step of `p` from `s`,
     *              and the program that is left to be executed.
     */
    function method stepEVMIR<S>(p: seq<EVMIRProg<S>>, s: S): (S, seq<EVMIRProg>) 
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
                // case Skip() => stepEVMIR(p[1..], s)
    }

    /**
     *  Semantics of EVMIR programs.
     *
     *  @param  g   A CFG.
     *  @param  pc  A node in the CFG.
     *  @param  s   A state.
     *  @returns    The state obtained after executing the instruction at node
     *              `pc` and the next `pc`. 
     */
    // function method stepCFG<S>(g: CFG, pc: nat, s: S): (S, nat) 
    //     requires pc in g.g
    // {   
    //     if pc == g.exit then (s, g.exit)
    //     else (s, pc) 
    //         match 
    //         // match p[0]
    //         //     case Block(i) => (runInst(i, s), p[1..])
    //         //     case While(c, b) => 
    //         //             if c(s) then
    //         //                 var (s', p') := stepEVMIR(b, s);
    //         //                 (s', p' + p)
    //         //             else 
    //         //                 (s, p[1..]) 
    //         //     case IfElse(c, b1, b2) => 
    //         //         if c(s) then 
    //         //             var (s', p') := stepEVMIR(b1, s);
    //         //             (s', p' + p[1..])
    //         //         else var (s', p') := stepEVMIR(b2, s);
    //         //             (s', p' + p[1..])
    //             // case Skip() => stepEVMIR(p[1..], s)
    // }

    /**
     *  Build the CFG of a EVMIR program.
     *
     *  @param  inCFG   The CFG to extend.
     *  @param  p       The program to build the CFG for.
     *  @param  k       First Id (number) available to id newly created state.
     *  @param  m       The simulation for inCFG.
     *  @param  c       The program that remains to be executed from the current point.
     *  @returns        The CFG `inCFG` extended from its final state (`k`) with the CFG of p, and
     *                  the simulation map extended to the newly created nodes.
     */
    function method toCFG<S>( 
            inCFG: CFG<S>, 
            p: seq<EVMIRProg<S>>, 
            k: nat, m: map<nat, seq<EVMIRProg<S>>>, 
            c: seq<EVMIRProg<S>> := p): (CFG<S>, nat, map<nat, seq<EVMIRProg<S>>>)
        requires |c| >= |p|
        decreases p 
    {
        if p == [] then 
            var finalCFG := inCFG.(g := inCFG.g[k := []]);
            (finalCFG, k, m)
        else 
            // Current node is associated with the program that is left to be run. 
            var m' := m[k := c];
            match p[0]
                case Block(i) => 
                    //  Build CFG of Block, append to previous graph, and then append graph of tail(p)
                    toCFG( 
                        CFG(inCFG.entry, 
                            inCFG.g[k := [(i, k + 1)]], // + [(k, k + 1, i)], 
                            k + 1),
                        p[1..],
                        k + 1,
                        m',
                        c[1..]  
                    )
                
                case IfElse(cond, b1, b2) => 
                    //  Add true and false edges to current graph
                    //  Build cfgThen starting numbering from k + 1 for condition true 
                    var (cfgThen, indexThen, m1) := toCFG(inCFG, b1, k + 1, m', b1 + c[1..]);
                    //  Build cfgElse starting numbering from indexThen + 1 for condition false
                    var (cfgThenElse, indexThenElse, m2) := toCFG(cfgThen, b2, indexThen + 1, m1, b2 + c[1..]);
                    //  Build IfThenElse cfg stitching together previous cfgs and 
                    //  wiring cfgThen.exit to cfgElse.exit with a skip instruction
                    var cfgIfThenElse := CFG(
                                            cfgThenElse.entry, 
                                            cfgThenElse.g[
                                                inCFG.exit := [(TestInst(cond, "TRUE"), k + 1), (TestInst(cond, "FALSE"), indexThen + 1)]
                                            ][
                                                cfgThen.exit := [(Skip(), cfgThenElse.exit)]
                                            ],
                                            cfgThenElse.exit
                                        );
                    toCFG( cfgIfThenElse, 
                            p[1..], 
                            indexThenElse, 
                            m2[indexThen := c[1..]],
                            c[1..]
                        )

                case While(cond, b) =>  
                    //  Build CFG for b from k + 1 when while condition is true 
                    var (whileBodyCFG, indexBodyExit, m3) := toCFG(inCFG, b, k + 1, m', b + c);
                    var cfgWhile := CFG(
                                        whileBodyCFG.entry, 
                                        whileBodyCFG.g[
                                            inCFG.exit := [(TestInst(cond, "TRUE"), k + 1), (TestInst(cond, "FALSE"), indexBodyExit + 1)]
                                        ][
                                            whileBodyCFG.exit := [(Skip(), k)]
                                        ],
                                        indexBodyExit + 1
                                        );
                    toCFG(cfgWhile, p[1..], indexBodyExit + 1, 
                        m3[indexBodyExit := c], 
                        c[1..])
    }
        
}
