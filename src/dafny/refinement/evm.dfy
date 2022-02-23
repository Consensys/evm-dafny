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
 *  EVM programs possibly with Jumps.
 */
module EVM {

    import opened EVMSeq 

    datatype EVM<!S> = 
            AInst(i: EVMInst)
        |   Jumpi(cond: S -> bool, tgt: nat)
        |   Jump(tgt: nat)

    /**
     *  Semantics of EVM programs.
     */
    function method runEVM<S>(pc: nat, p: map<nat, EVM>, s: S, n: nat): (S, nat)
        decreases n 
    {
        if pc == 0 || n == 0 || pc !in p then (s, 0)
            //  We could have different types of termination
        else 
            //  Execute instruction at PC and increment PC accordingly
            match p[pc] 
                case AInst(Inst(i)) => 
                    runEVM(pc + 1, p, i(s), n - 1)
                case Jumpi(c, tgt) => 
                    if !c(s) then runEVM(pc + 1, p, s, n - 1) else runEVM(tgt, p, s, n - 1)
                case Jump(tgt) => 
                    runEVM(tgt, p, s, n - 1) 
    }

}
