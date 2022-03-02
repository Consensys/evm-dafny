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
 *  Provides EVM programs with Jumps.
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
     *  @note   Jump values are relative to address the instruction is at.
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
     *  Compute the state after executing a given number of intructions.
     *
     *  @param  pc  Initial PC.
     *  @param  p   The program to be executed.
     *  @param  s   The initial state.
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
                case AInst(i)       =>  runEVM2(pc + 1, p, runInst(i, s), n - 1)
                case Jumpi(c, tgt)  =>  if !c(s) then runEVM2(pc + 1, p, s, n - 1) 
                                        else runEVM2(pc + tgt, p, s, n - 1)
                case Jump(tgt)      =>  runEVM2(pc + tgt, p, s, n - 1) 
    }

    /**
     *  All jumps are close jumps.
     *
     *  @param  p   A program.
     *  @returns    Whether all instructions in `p` are clode jumps.
     */
    predicate isClosed(p: seq<EVMProg2>)
    {
        forall i :: 0 <= i < |p| ==> closeJump(p, i)
    }

    /**
     *  Whether an instruction transfers control within a program boundary.
     *  
     *  @param  p   A program which is a sequence of instructions.
     *  @param  i   The index of an instruction in `[`.
     *  @returns    Whether `p[i]` trasfers control to an instruction in 0..p.
     *
     *  @note       The boundary is considered to be 0..p - 1 which are
     *              program's instructions locations and `p` which corresponds to
     *              the program's end point (termination).  
     */
    predicate closeJump(p: seq<EVMProg2>, i: nat)
        requires 0 <= i < |p| 
    {
        match p[i]
                case Jumpi(cond, tgt)   => 0 <= i + tgt <= |p| 
                case Jump(tgt)          => 0 <= i + tgt <= |p| 
                case _                  => true
    }

    /**
     *  The execution of n steps of a closed program |p| either termninates with 
     *  pc in 0..|p| - 1 and n == 0 or pc == |p| and n >= 0 
     */
    lemma foo303<S>(pc: nat, p: seq<EVMProg2>, s: S, n:nat) 
        requires isClosed(p)
        requires 0 <= pc <= |p|
        ensures 0 <= runEVM2<S>(pc, p, s, n).1 <= |p|
        decreases n 
        // ensures (0 <= runEVM2<S>(pc, p, s, n).1 < |p| ==> n == 0)
        //         (runEVM2<S>(pc, p, s, n).1 == |p| ==> n >= 0)  
    {
        if |p| == pc || n == 0 {
            //  
        } else {
            assert pc < |p|; 
            match p[pc] 
                case AInst(i)           =>  
                    foo303(pc + 1, p, runInst(i, s), n - 1);
                case Jumpi(cond, tgt)   =>  
                    assert closeJump(p, pc);
                    assert 0 <= pc + tgt <= |p|;
                    foo303(if cond(s) then pc + tgt else pc + 1, p, s, n - 1);
                case Jump(tgt) => 
                    assert closeJump(p, pc);
                    assert 0 <= pc + tgt <= |p|;
                    foo303(pc + tgt, p, s, n - 1);
        }
    }
}
