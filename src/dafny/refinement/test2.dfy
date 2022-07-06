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

        /** 
          *  build labelled DiGrapwh and print label which is a string
          */
        var j : nat -> nat := x => x + 1;
        var i : EVMInst<nat> := Inst( j, "ADD");     

        var g1 : LabDiGraph<nat> := map[
            0 := [(i, 1)], 
            1 := [(i, 2)],
            2 := []
        ];

        var k : CFG<nat> := CFG(0, g1, 2); 
        printCFG(k, "p1", map[]);  
      
        print "\n";

    }