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
        // var i := Inst(x => x + 1, "one");
        // var p := toEVM([Block(i)]);
        // display(p);

        var g1 : LabDiGraph := [LabDiEdge(0, 1, "edge"), 
            LabDiEdge(1, 2, "edge2"), 
            LabDiEdge(1, 3, "edge3"),
            LabDiEdge(2, 0, "loop")];
        var k := CFG(0, g1, 2); 

        printCFG(k);  
        var i := Inst((x:int) => x + 1, "add");     
        var p1 := EVMIRProg2.IfElse(true, [EVMIRProg2.Block(i)], [EVMIRProg2.Block(i)]); 

        /*
         *  build labelled DiGraph and print label which is a string
        */
    }