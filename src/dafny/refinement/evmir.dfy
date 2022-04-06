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
        //  Ignore the status of the pretty-printing
        var x := diGraphToDOT<S>(cfg.g, cfg.exit + 1, name, toTooltip(m, cfg.exit));  
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
    function method stepCFG<S>(g: CFG, pc: nat, s: S): (S, nat) 
        requires pc in g.g
    {   
        (s,0)
        // if pc == g.exit then (s, g.exit)
        // else (s, pc) 
        //     // match 
        //     match p[0]
        //         case Block(i) => (runInst(i, s), p[1..])
                // case While(c, b) => 
                //         if c(s) then
                //             var (s', p') := stepEVMIR(b, s);
                //             (s', p' + p)
                //         else 
                //             (s, p[1..]) 
                // case IfElse(c, b1, b2) => 
                //     if c(s) then 
                //         var (s', p') := stepEVMIR(b1, s);
                //         (s', p' + p[1..])
                //     else var (s', p') := stepEVMIR(b2, s);
                //         (s', p' + p[1..])
                // case Skip() => stepEVMIR(p[1..], s)
    }

    /**
     *  @param  m   A map.
     *  @param  k   A number.
     *  @returns    Whether k.Keys == 0..k - 1   
     */
    predicate keysEqualRange<S>(m: map<nat, S>, k: nat) 
    {
        &&  |m| == k
        &&  (forall key:: key in m <==> 0 <= key < |m|)
    }

    /** Node types determine the number of outgoing edges. */
    predicate correctOutgoingEdges<S>(c: CFG<S>, m: map<nat, seq<EVMIRProg<S>>>)
        /** Each CFG has at least an initial node. */
        requires |c.g| >= 1
        /** The nodes in c are within 0..|c.g| - 1 */
        requires keysEqualRange(m, |c.g|)
    {
        // assert forall key:: key in m <==> 0 <= key < |c.g|;
        assert |c.g| - 1 in m;
        //  last node is the Nil program.
        m[|c.g| - 1] == []
        // true
    }

    /** A valid CFG. 
     *  
     *  The nodes of the CFG should exactly be the interval 0..|c.g| - 1.
     *  The exit node is the last one.
     */
    predicate validCFG<S>(c: CFG<S>) 
    {
        &&  0 in c.g // we could use |c.g| > 0 too.
        &&  (forall key:: key in c.g <==> 0 <= key < |c.g|) //  c.g.Keys == 0..|c.g| - 1
        // &&  c.exit in c.g 
        &&  c.exit == |c.g| - 1 //  last node is c.g the exit node of c
        &&  c.g[c.exit] == []   //  last node is a sink node
        &&  c.entry in c.g      //  entry node muts be in c.g
    }

    //  Lemmas for maps
    lemma foo101<S>(m: map<nat, S>, k: nat, s: S)
        requires  (forall key:: key in m <==> 0 <= key < |m|)
        requires k >= |m|
        ensures m[k := s].Keys == m.Keys + { k }
        ensures |m[k := s]| == |m| + 1
    {

    }

    lemma foo202<S>(m: map<nat, S>, k: nat, s: S)
        requires k in m.Keys
        ensures |m[k := s]| == |m|
    {

    }

    /**
     *  Build the CFG of a EVMIR program.
     *
     *  @param  inCFG   The CFG to extend.
     *  @param  p       The program to build the CFG for.
     *  @param  k       First Id (number) available to id newly created nodes.
     *  @param  m       The simulation map for inCFG.
     *  @param  c       The program that remains to be executed from the current point.
     *  @returns        The CFG `inCFG` extended from its final state (`k`) with the CFG of p, and
     *                  the simulation map extended to the newly created nodes.
     *                  r.0.g nodes range from 0 to r.1 (excluded). r.1. is the first number available 
     *                  to create new nodes. 
     *
     *  @note           The inCFG is the CFG built so far. 
     *                  inCFG.exit should be equal to k, and 
     *                  k is |inCFG.g| - 1 and
     *                  the keys in inCFG.g should be 0..k (k + 1 keys)
     *                  The map m should be defined for exactly the same keys in inCFG.g.Keys 
     *                  
     *                  m is map from all the nodes of inCFG.g to programs.
     */
    function method toCFG<S>(  
            inCFG: CFG<S>, 
            p: seq<EVMIRProg<S>>, 
            k: nat, 
            m: map<nat, seq<EVMIRProg<S>>>, 
            c: seq<EVMIRProg<S>> := p): (r: (CFG<S>, nat, map<nat, seq<EVMIRProg<S>>>))
        requires |c| >= |p|

        requires validCFG(inCFG)
        requires k + 1 == |inCFG.g|

        ensures validCFG(r.0)
        ensures r.1 + 1 == |r.0.g|

        decreases p 
    {
        if p == [] then 
            (inCFG, k, m)
        else 
            //  Each node is associated with a program via m. 
            match p[0]
                case Block(i) => 
                    //  Add an edge k -> k + 1 to inCFG and set outgoing transitions of k + 1 to []
                    var c1 :=  CFG(inCFG.entry, inCFG.g[k := [(i, k + 1)]][k + 1 := []], k + 1);
                    //  New exit node is k + 1
                    //  Build CFG of remaining program from c1.exit

                    // calc ==> {
                    //     |inCFG.g| == k + 1;
                    //     { assert validCFG(inCFG); }
                    //     k in inCFG.g.Keys;
                    //     // k + 1 !in inCFG.g.Keys;
                    // }
                    // assert k + 1 == |inCFG.g| ;
                    // assert k in inCFG.g.Keys;
                    // foo202(inCFG.g, k, [(i, k + 1)]);
                    // foo101(inCFG.g[k := [(i, k + 1)]], k + 1, []); 
                    // assert |c1.g| == |inCFG.g[k := [(i, k + 1)]][k + 1 := []]| == k + 2;
                    // assert inCFG.g[k + 1 := []].Keys == inCFG.g.Keys + {k + 1};
                    // assert validCFG(c1);
                    var r := toCFG( 
                        c1,
                        p[1..],
                        k + 1,
                        m[k + 1 := c[1..]],    //  program remaining from exit node is c[1..]
                        c[1..]  
                    );
                    //  Proof 
                    r

                case IfElse(cond, b1, b2) =>  
                    //  Add new exit node k + 1 and build CFG for cond True
                    assert validCFG(inCFG.(exit := k + 1));
                    var (cfgThen, indexThen, m1) := toCFG(inCFG.(exit := k + 1), b1, k + 1, m[k + 1 := b1 + c[1..]], b1 + c[1..]);
                    //  Exit node and last number used is indexThen.
                    //  Build cfgElse for cond false starting numbering from indexThen + 1
                    assume validCFG(cfgThen.(exit := indexThen + 1));
                    var (cfgThenElse, indexThenElse, m2) := toCFG(cfgThen.(exit := indexThen + 1), b2, indexThen + 1, m1[indexThen + 1 := b2 + c[1..]], b2 + c[1..]);
                    //  Build IfThenElse CFG stitching together previous Then and Else graphs 
                    //  and wiring cfgThen.exit to cfgElse.exit with a skip instruction
                    var cfgIfThenElse := 
                                CFG(
                                    cfgThenElse.entry, 
                                    cfgThenElse.g[
                                        inCFG.exit := [(TestInst(cond, "TRUE"), k + 1), (TestInst(cond, "FALSE"), indexThen + 1)]
                                    ][
                                        cfgThen.exit := [(Skip(), cfgThenElse.exit)]
                                    ],
                                    cfgThenElse.exit
                                );
                    //  Build CFG of remaining program from indexThenElse
                    assume validCFG(cfgIfThenElse);
                    var r := toCFG(
                            cfgIfThenElse, 
                            p[1..], 
                            indexThenElse, 
                            m2[indexThenElse := c[1..]],
                            c[1..]
                        );
                    r

                case While(cond, b) =>  
                    //  Add node k + 1 
                    var tmpCFG := inCFG.(exit := k + 1, g := inCFG.g[k + 1 := []]);
                    //  Build CFG of b (condition is true) from k + 1
                    assume validCFG(tmpCFG);
                    var (whileBodyCFG, indexBodyExit, m3) := toCFG(tmpCFG, b, k + 1, m[k + 1 := b + c], b + c);
                    //  Add edges k -- True -> k + 1, k -- False -> indexBodyExit + 1, indexBodyExit -- Skip -> k
                    //  Make indexBodyExit + 1 the new exit node (end of the loop) 
                    var cfgWhile := CFG(
                                        whileBodyCFG.entry, 
                                        whileBodyCFG.g[
                                            inCFG.exit := [(TestInst(cond, "TRUE"), k + 1), (TestInst(cond, "FALSE"), indexBodyExit + 1)]
                                        ][
                                            whileBodyCFG.exit := [(Skip(), k)]
                                        ][
                                            indexBodyExit + 1 := []
                                        ],
                                        indexBodyExit + 1
                                        );
                    // Build remaining from exit node indexBodyExit + 1
                    assume validCFG(cfgWhile);
                    var r := toCFG(
                        cfgWhile, 
                        p[1..], 
                        indexBodyExit + 1, 
                        m3[indexBodyExit + 1 := c[1..]], 
                        c[1..]);
                    r
    }
        
}
