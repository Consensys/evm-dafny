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
include "../utils/Helpers.dfy"

/**
 *  Provides proofs that EVM code simulates some corresponding EVMIR code.
 */
module EVMIRSimulationFull {

    import opened EVMSeq
    import opened EVMIR 
    import opened EVM 
    import opened Helpers

    //  General proofs
    //  For this we need to define a translation from EVM-IR to EVM

    /**
     *  Translate and EVMir program into a EVM program.
     */
    function method toEVM<S>(p: EVMIRProg): map<nat, EVMProg>
    {
        match p 
            case Block(i) => map[1 := AInst(i)]
            case While(c, Block(b)) => 
                map[
                    1 := Jumpi(negF(c), 3), 
                    2 := AInst(b),
                    3 := Jump(1)
                ]
            case _ => map[]
    }
        

}
