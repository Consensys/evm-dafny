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
 
include "../utils/Graphs.dfy"
include "./evmir.dfy"  
include "evm-seq.dfy"

import opened Graphs
import opened EVMIR 
import opened EVMSeq


method {:verify true} Main() {

        /*
         *  build labelled DiGraph and print label which is a string
         */
        // var g1 : LabDiGraph := [
        //     (0, 1, "edge"), 
        //     (1, 2, "edge2"), 
        //     (1, 3, "edge3"),
        //     (2, 0, "loop")]; 
        // var k := CFG(0, g1, 2); 
        // // printCFG(k);   

        //  For some reasons inlining the function into Inst
        //  creates a type problem ... or partial function problem.
        //  So we create a function first and then use it in instructions.
        var addOne : nat -> nat := x => x + 1;

        var i := Inst(addOne, "ADD");     
        var p1 := EVMIRProg.IfElse(_ => true, [EVMIRProg.Block(i)], [EVMIRProg.Block(i)]); 

        //  Sequence of blocks 
        var i1 := Inst(addOne, "SUB");     
        var p2 := [EVMIRProg.Block(i1), EVMIRProg.Block(i1), EVMIRProg.Block(i1)];
        // var (cfg2, max2, m2) := toCFG(CFG(0, map[0 := []], 0), p2, 0, map[0 := p2]);
        // printCFG(cfg2, "p2", m2);    
        // printCFGmap(m2);

        //  IfThenElse 
        var i2 := Inst(addOne, "PUSH");     
        var i3 := Inst(addOne, "POP");     
        var p3 := EVMIRProg.IfElse(_ => true, [EVMIRProg.Block(i1), EVMIRProg.Block(i2)], [EVMIRProg.Block(i2),  EVMIRProg.Block(i1)]); 
        // var (cfg3, max3, m3) := toCFG2(CFG2(0, map[], 0), [p3] + [EVMIRProg.Block(i3)], 0, map[]);
        // printCFG(cfg3, "ifThenElse", m3);   
        // printCFGmap(m3);

        //  While loop
        var p4 := EVMIRProg.While(_ => true, [EVMIRProg.Block(i1), EVMIRProg.Block(i1)]); 
        // var (cfg4, max4, m4) := toCFG2(CFG2(0, map[], 0), [p4] + [EVMIRProg.Block(i3)], 0, map[]);
        // printCFG(cfg4, "CFG for While true do add; PUSH; od", m4);   
        // printCFGmap(m4);

        //  A more complicated program
        var p5 := EVMIRProg<nat>.IfElse(_ => true, [EVMIRProg.Block(i1)], [EVMIRProg.Block(i2)]); 
        var p6 := EVMIRProg<nat>.While(_ => true, [EVMIRProg.Block(i1), p5, EVMIRProg.Block(i2)]); 
        // var p6 := EVMIRProg.While(true, [p5]); 
        var (cfg6, max6, m6) := toCFG(CFG(0, map[0 := []], 0), [p6], 0, map[0 := [p6]]);
        printCFG(cfg6, "CFG for While true do {if then else} od", m6);   
        // printCFGmap(m6);

        // print "Pretty-print\n";
        // print prettyEVMIR([p6]);
        print "\n";

    }