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

include "./evm-seq.dfy"
include "./evmir.dfy"
include "./evm.dfy"

module EVMIRTests { 

    import opened EVMSeq
    import opened EVMIR
    import opened EVM 

    //  Tests

    //  State is one counter
    datatype S1 = S1(k: nat)

    //  Addition
    function method add(x: S1): S1 
    {
        S1(x.k + 1)
    }

    method Main() 
    {
        //  Run a simple EVM program p1
        var p1 := map[
            1 := AInst(Inst(add))
        ];

        var s0 := S1(14);
        var s1:= runEVM(1, p1, s0, 1);
        print s1, "\n";

        //  run p2 EVMIR - a while loop
        s0 := S1(0);
        var p2 := While( (x:S1) => x.k < 7, Inst((x:S1) => S1(x.k + 1)));
        var r2 := runEVMIR([p2], s0, 20);
        print r2, "\n";

        //  Program with jumps to simulate p2 – EVM 
        var p3 := map[
            1 := Jumpi((x:S1) => x.k > 7, 0),
            2 := AInst(Inst(add)),
            3 := Jump(1)
        ];

        var r3 := runEVM(1, p3, s0, 20);
        print r3, "\n";

    }
}

