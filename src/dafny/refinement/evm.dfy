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

    // datatype EVMProg<!S> = 
    //         AInst(i: EVMInst)
    //     |   Jumpi(cond: S -> bool, tgt: nat)
    //     |   Jump(tgt: nat)

    /**
     *  EVM instructions.
     *
     *  @note   Jump values are relative to address the instruction is at.
     */
    datatype EVMProg2<!S> = 
            AInst(i: EVMInst)
        |   Jumpi(cond: S -> bool, tgt: int)    
        |   Jump(tgt: int)
        // |   Nop()

    /**
     *  Run one step of a program.
     *  
     *
     *  @note   If the `pc` is outside the set of instructions, stop.
     */
    function method stepEVM<S>(pc: nat, p: seq<EVMProg2>, s: S): (int, S)
    {
        if pc < 0 || pc >= |p| then  
            (pc, s)
        else 
            match p[pc] 
                case AInst(i)       =>  (pc + 1, runInst(i, s))
                case Jumpi(c, tgt)  =>  if !c(s) then (pc + 1, s) 
                                        else (pc + tgt, s)
                case Jump(tgt)      =>  (pc + tgt, s) 
                // case Nop()          =>  (pc + 1, s)

    }

    function method stepEVM2<S, T>(pc: int, p: seq<(EVMProg2, T)>, s: S): (int, S)
    {
        if pc < 0 || pc >= |p| then  
            (pc, s)
        else 
            match p[pc].0 
                case AInst(i)       =>  (pc + 1, runInst(i, s))
                case Jumpi(c, tgt)  =>  if !c(s) then (pc + 1, s) 
                                        else (pc + tgt, s)
                case Jump(tgt)      =>  (pc + tgt, s) 
                // case Nop()          =>  (pc + 1, s)

    }

    /**
     *  Semantics of EVM programs.
     */
    // function method runEVM<S>(pc: nat, p: map<nat, EVMProg>, s: S, n: nat): (S, nat)
    //     decreases n 
    // {
    //     if pc == 0 || n == 0 || pc !in p then (s, 0)
    //         //  We could have different types of termination
    //     else 
    //         //  Execute instruction at PC and increment PC accordingly
    //         match p[pc] 
    //             case AInst(i) => 
    //                 runEVM(pc + 1, p, runInst(i, s), n - 1)
    //             case Jumpi(c, tgt) => 
    //                 if !c(s) then runEVM(pc + 1, p, s, n - 1) 
    //                 else runEVM(tgt, p, s, n - 1)
    //             case Jump(tgt) => 
    //                 runEVM(tgt, p, s, n - 1) 
    // }

    /**
     *  Compute the state after executing a given number of intructions.
     *
     *  @param  pc  Initial PC.
     *  @param  p   The program to be executed.
     *  @param  s   The initial state.
     *  @param  n   The maximum number of steps to be executed.
     *  @returns    The state reached from `s` by executing at most `n` steps of `p` and 
     *              the last pc.
     *
     *  @note       In this semantics `jumps` are relative i.e. `jump(k)` updates the 
     *              `pc` to `pc + k`.
     *  
     */
    // function method runEVM2<S>(pc: int, p: seq<EVMProg2>, s: S, n: nat): (S, nat)
    //     decreases n 
    // {
    //     if n == 0 || pc >= |p| || pc < 0 then (s, |p|)
    //         //  We could have different types of termination.
    //     else 
    //         //  Execute instruction at PC and increment PC accordingly.
    //         match p[pc] 
    //             case AInst(i)       =>  runEVM2(pc + 1, p, runInst(i, s), n - 1)
    //             case Jumpi(c, tgt)  =>  if !c(s) then runEVM2(pc + 1, p, s, n - 1) 
    //                                     else runEVM2(pc + tgt, p, s, n - 1)
    //             case Jump(tgt)      =>  runEVM2(pc + tgt, p, s, n - 1) 
    // }

    //  returns s', pc', n'
    // function method runEVM3<S>(pc: int, p: seq<EVMProg2>, s: S, n: nat): (S, int, nat)
    //     decreases n 
    // {
    //     if n == 0 || pc >= |p| || pc < 0 then (s, pc, n)
    //         //  We could have different types of termination.
    //     else 
    //         //  Execute instruction at PC and increment PC accordingly.
    //         match p[pc] 
    //             case AInst(i)       =>  runEVM3(pc + 1, p, runInst(i, s), n - 1)
    //             case Jumpi(c, tgt)  =>  if !c(s) then runEVM3(pc + 1, p, s, n - 1) 
    //                                     else runEVM3(pc + tgt, p, s, n - 1)
    //             case Jump(tgt)      =>  runEVM3(pc + tgt, p, s, n - 1) 
    // }

    

    /**
     *  All jumps are close jumps.
     *
     *  @param  p   A program.
     *  @returns    Whether all instructions in `p` are clode jumps.
     */
    // predicate isClosed(p: seq<EVMProg2>)
    // {
    //     forall i :: 0 <= i < |p| ==> closeJump(p, i)
    // }

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
    // predicate closeJump(p: seq<EVMProg2>, i: nat)
    //     requires 0 <= i < |p| 
    // {
    //     match p[i]
    //             case Jumpi(cond, tgt)   => 0 <= i + tgt <= |p| 
    //             case Jump(tgt)          => 0 <= i + tgt <= |p| 
    //             case _                  => true
    // }

    /**
     *  The execution of n steps of a closed program |p| either termninates with 
     *  pc in 0..|p| - 1 and n == 0 or pc == |p| and n >= 0.
     *
     *  @param  pc  An initial pc.
     *  @param  p   An EVM program.
     *  @param  s   An initial state.
     *  @param  n   The maximum number of steps to be executed.
     */
    // lemma pcBoundsOnTermination<S>(pc: nat, p: seq<EVMProg2>, s: S, n: nat) 
    //     requires isClosed(p)
    //     requires 0 <= pc <= |p|
    //     ensures 0 <= runEVM3<S>(pc, p, s, n).1 <= |p|
    //     ensures 0 <= runEVM3<S>(pc, p, s, n).1 < |p| ==> runEVM3<S>(pc, p, s, n).2 == 0 
    //     ensures runEVM3<S>(pc, p, s, n).1 == |p| ==> runEVM3<S>(pc, p, s, n).2 >= 0  
    //     decreases n 
    // {
    //     if |p| == pc || n == 0 {
    //         //  Thanks Dafny
    //     } else {
    //         assert pc < |p|; 
    //         match p[pc] 
    //             case AInst(i)           =>  
    //                 pcBoundsOnTermination(pc + 1, p, runInst(i, s), n - 1);
    //             case Jumpi(cond, tgt)   =>  
    //                 assert closeJump(p, pc);
    //                 assert 0 <= pc + tgt <= |p|;
    //                 pcBoundsOnTermination(if cond(s) then pc + tgt else pc + 1, p, s, n - 1);
    //             case Jump(tgt)          => 
    //                 assert closeJump(p, pc);
    //                 assert 0 <= pc + tgt <= |p|;
    //                 pcBoundsOnTermination(pc + tgt, p, s, n - 1);
    //     }
    // }

    // lemma localProp<S>(pc: nat, p: seq<EVMProg2>, s: S, k1: nat, k2: nat)
    //     requires 0 <= k1 < k2 < |p|
    //     requires isClosed(p[k1..k2])
    //     requires k1 <= pc < k2
    //     ensures k1 <= stepEVM(pc, p, s).0 <= k2 
    //     // decreases n
    // {
    //     if false {
    //         //  Thanks Dafny
    //     } else if pc == k2 { 
    //         // calc <= {
    //         //     runEVM3(pc, p, s, n).1;
    //         //     runEVM3(pc, p[k1..k2], s, n).1;
    //         //     // { assert isClosed(p[k1..k2]) ;}
    //         //     // k2;
    //         // }
    //     } else {
    //         assert k1 <= pc < k2; 
    //         match p[pc] 
    //             case AInst(i)           =>  
    //                 // localProp(pc + 1, p, runInst(i, s), k1, k2);
    //                 // assume k1 <= runEVM3(k1, p, s, n).1 <= k2 ;
    //                 // pcBoundsOnTermination(pc + 1, p, runInst(i, s), n - 1);
    //             case Jumpi(cond, tgt)   =>  
    //                 // assert closeJump(p, pc);
    //                 assume k1 <= stepEVM(pc, p, s).0 <= k2 ;
    //                 // assert 0 <= pc + tgt <= |p|;
    //                 // pcBoundsOnTermination(if cond(s) then pc + tgt else pc + 1, p, s, n - 1);
    //             case Jump(tgt)          => 
    //                 // assume k1 <= stepEVM(pc, p, s).0 <= k2 ;
    //                 calc == {
    //                     p[pc];
    //                     p[k1..k2][pc - k1];
    //                 }
    //                 calc == {
    //                     stepEVM(pc, p, s);
    //                     (pc + tgt, s);
    //                     calc == {
    //                         p[pc];
    //                         p[k1..k2][pc - k1];
    //                     }
    //                     stepEVM(pc - k1, p[k1..k2], s);
    //                     // (pc + tgt, s);
    //                 }
    //                 calc == {
    //                     stepEVM(pc - k1, p[k1..k2], s).0;
    //                     pc - k1 + tgt;
    //                     // calc == {
    //                     //     p[pc];
    //                     //     p[k1..k2][pc - k1];
    //                     // }

    //                 }
    //                 assume k1 <= stepEVM(pc, p, s).0 <= k2 ;
    //                 // assert closeJump(p[k1..k2], pc);
    //                 // assert 0 <= pc + tgt <= |p|;
    //                 // pcBoundsOnTermination(pc + tgt, p, s, n - 1);
    //                 // assume k1 <= runEVM3(k1, p, s, n).1 <= k2 ;
    //     }   
    // } 
}
