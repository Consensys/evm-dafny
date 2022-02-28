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
 *  Provides EVM programs possibly with Jumps.
 */
module EVM {

    import opened EVMSeq 

    datatype EVMProg<!S> = 
            AInst(i: EVMInst)
        |   Jumpi(cond: S -> bool, tgt: nat)
        |   Jump(tgt: nat)

    /**
     *  EVM instructions.
     *
     *  @note   Jump values are relatove to pc the instruction is at.
     */
    datatype EVMProg2<!S> = 
            AInst(i: EVMInst)
        |   Jumpi(cond: S -> bool, tgt: int)    
        |   Jump(tgt: int)

    /**
     *  Semantics of EVM programs.
     */
    function method runEVM<S>(pc: nat, p: map<nat, EVMProg>, s: S, n: nat): (S, nat)
        decreases n 
    {
        if pc == 0 || n == 0 || pc !in p then (s, 0)
            //  We could have different types of termination
        else 
            //  Execute instruction at PC and increment PC accordingly
            match p[pc] 
                case AInst(i) => 
                    runEVM(pc + 1, p, runInst(i, s), n - 1)
                case Jumpi(c, tgt) => 
                    if !c(s) then runEVM(pc + 1, p, s, n - 1) 
                    else runEVM(tgt, p, s, n - 1)
                case Jump(tgt) => 
                    runEVM(tgt, p, s, n - 1) 
    }

    /**
     *  A program is a sequence of EVM instructions.
     *
     *  @param  pc  (Current) PC.
     *  @param  p   The program to be executed.
     *  @param  s   The (current) state.
     *  @param  n   The maximum number of steps to be executed.
     *  @returns    The state reached from `s` by executing at most `n` steps of `p`.
     *
     *  @note       In this semantics `jumps` are relative i.e. `jump(k)` updates the 
     *              `pc` to `pc + k`.
     *  
     */
    function method runEVM2<S>(pc: int, p: seq<EVMProg2>, s: S, n: nat): (S, nat)
        decreases n 
    {
        if n == 0 || pc >= |p| || pc < 0 then (s, |p|)
            //  We could have different types of termination.
        else 
            //  Execute instruction at PC and increment PC accordingly.
            match p[pc] 
                case AInst(i) => 
                    //  Run rest of program from `pc` + 1 from state obtained after executing `i`
                    runEVM2(pc + 1, p, runInst(i, s), n - 1)
                case Jumpi(c, tgt) => 
                    //  Conditional jump. If `cond` true the jump otherwise continue to next instruction.
                    if !c(s) then runEVM2(pc + 1, p, s, n - 1) 
                    else runEVM2(pc + tgt, p, s, n - 1)
                case Jump(tgt) => 
                    //  Unconditional jump.
                    runEVM2(pc + tgt, p, s, n - 1) 
    }

}
