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


method {:verify false} Main() {

        /*
         *  build labelled DiGraph and print label which is a string
         */
        var g1 : LabDiGraph := [
            (0, 1, "edge"), 
            (1, 2, "edge2"), 
            (1, 3, "edge3"),
            (2, 0, "loop")]; 
        var k := CFG(0, g1, 2); 
        printCFG(k);  

        var i := Inst((x:int) => x + 1, "ADD");     
        var p1 := EVMIRProg.IfElse(_ => true, [EVMIRProg.Block(i)], [EVMIRProg.Block(i)]); 

        //  Sequence of blocks
        var i1 := Inst((x:nat) => x + 1, "SUB");     
        var p2 := [EVMIRProg.Block(i1), EVMIRProg.Block(i), EVMIRProg.Block(i)];
        var (cfg2, max2) := toCFG(CFG(0, [], 0), p2, 0);
        printCFG(cfg2);   

        //  IfThenElse 
        var i2 := Inst((x:nat) => x + 1, "PUSH");     
        var i3 := Inst((x:nat) => x + 1, "POP");     
        var p3 := EVMIRProg.IfElse(_ => true, [EVMIRProg.Block(i1), EVMIRProg.Block(i2)], [EVMIRProg.Block(i2)]); 
        var (cfg3, max3) := toCFG(CFG(0, [], 0), [p3] + [EVMIRProg.Block(i3)], 0);
        printCFG(cfg3);   

        //  While loop
        var p4 := EVMIRProg.While(_ => true, [EVMIRProg.Block(i1), EVMIRProg.Block(i)]); 
        var (cfg4, max4) := toCFG(CFG(0, [], 0), [p4] + [EVMIRProg.Block(i3)], 0);
        printCFG(cfg4, "CFG for While true do add; PUSH; od");   

        //  A more complicated program
        var p5 := EVMIRProg.IfElse(_ => true, [EVMIRProg.Block(i1)], [EVMIRProg.Block(i2)]); 
        var p6 := EVMIRProg.While(_ => true, [EVMIRProg.Block(i1), p5, EVMIRProg.Block(i2)]); 
        // var p6 := EVMIRProg.While(true, [p5]); 
        var (cfg6, max6) := toCFG(CFG(0, [], 0), [p6], 0);
        printCFG(cfg6, "CFG for While true do {if then else} od");   

    }