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
 *  Provides proofs that EVM code simulates the corresponding EVMIR code.
 */
module EVMIRSimulationFull {

    import opened EVMSeq
    import opened EVMIR 
    import opened EVM 
    import opened Helpers

    //  General proofs
    //  For this we need to define a translation from EVM-IR to EVM

    function method continuationClosure<S>(p: seq<(EVMProg2, seq<EVMIRProg>)>, p1:  seq<EVMIRProg>):
        seq<(EVMProg2, seq<EVMIRProg>)>
    {
        if p == [] then 
            []
        else 
            [(p[0].0, p[0].1 + p1)]
            + continuationClosure(p[1..], p1) 
    }

    /**
     *  Translate and EVMIR program into a EVM program.
     *
     *  @param  p   An EVMIR program.
     *  @returns    Its translation into EVM (while and if are mapped to jumps).
     */
    function method toEVM<S>(p: seq<EVMIRProg>): seq<(EVMProg2, seq<EVMIRProg>)> 
    {
        if p == [] then 
            []
        else 
            match p[0]
                case Block(i) => 
                    [(EVMProg2.AInst(i), p)] + toEVM(p[1..])

                case While(c, b) => 
                    //   Translate b into EVM. xbb goes from 0 to |xbb| - 1
                    var xbb := toEVM(b);   
                    //  translation of While is 0 -> jumpi, 1..|xbb| xbb, xbb + 1 -> Jump
                    [(EVMProg2.Jumpi(negF(c), |xbb| + 2), p)] +  //  0 
                        continuationClosure(xbb, p) +            //  1..|xbb|
                    [(EVMProg2.Jump(-(|xbb| + 1)), p)]           //  |xbb| + 1
                    +  toEVM(p[1..])

                case IfElse(cond, xb1, xb2) => 
                    var xbb1 := toEVM(xb1);
                    var xbb2 := toEVM(xb2);
                    [(EVMProg2.Jumpi(negF(cond), |xbb1| + 2), p)] +  // 0 
                        continuationClosure(xbb1, p[1..]) +                     // 1..|xbb1|
                    [(EVMProg2.Jump(|xbb2| + 1), p[1..])] +                     //  |xbb1| + 1
                        continuationClosure(xbb2, p[1..])                       //  |xbb1| + 2 to |xbb1| + 2 + |xbb2| - 1
                    +  toEVM(p[1..])
    }

    predicate equiv<S>(p:  seq<(EVMProg2, seq<EVMIRProg>)>, s1: (S, int), s2: (S, seq<EVMIRProg>))
    {
        (0 <= s1.1 < |p| &&  s1.0 == s2.0 &&  p[s1.1].1 == s2.1)
        ||
        (s1.1 == |p| && s2.1 == [])
    }   

    lemma simulation<S>(p: seq<EVMIRProg>, p1: seq<EVMIRProg>, pevm: seq<(EVMProg2, seq<EVMIRProg>)>, s: S, pc: nat) 
        requires pevm == toEVM(p)
        requires 0 <= pc <= |pevm|
        requires equiv(pevm, (s, pc), (s, p1))
        ensures 
            var (pc1', s1') := stepEVM2(pc, pevm, s);
            var (s2', p2') := stepEVMIR(p1, s);
            equiv(pevm, (s1', pc1'), (s2', p2')) 
    {
        if pc == |pevm| {
            //  
        } else {
            //  Execute instruction at pc
            var (pc1', s1') := stepEVM2(pc, pevm, s);
            var (s2', p2') := stepEVMIR(p1, s);

            assume equiv(pevm, (s1', pc1'), (s2', p2'));
        }

    } 
    // lemma simul<S>(p: seq<(EVMProg2, seq<EVMIRProg>)>, s1: (S, int), s2: (S, seq<EVMIRProg>))
    //     requires 0 <= s1.1 < |p| 
    //     requires equiv(p, s1, s2)
    //     ensures 
    //         var (pc1', s1') := stepEVM2(s1.1, p, s1.0);
    //         var (s2', p2') := stepEVMIR(s2.1, s2.0);
    //         equiv(p, (s1', pc1'), (s2', p2')) 
    // {
    //     var (pc1', s1') := stepEVM2(s1.1, p, s1.0);
    //     var (s2', p2') := stepEVMIR(s2.1, s2.0);
    //     assume equiv(p, (s1', pc1'), (s2', p2')) ;
    // }

    lemma simul1<S>(s1: (S, nat), p: seq<(EVMProg2, seq<EVMIRProg>)>, i: EVMInst, s2: (S, seq<EVMIRProg>)) 
        // requires  p == [(EVMProg2.AInst(i), [Block(i)])]
        requires  p == toEVM([Block(i)])
        requires  equiv(p, (s1.0, s1.1), (s2.0, s2.1))
        ensures |p| == 1 
        ensures 
            var (pc1', s1') := stepEVM2(s1.1, p, s1.0);
            var (s2', p2') := stepEVMIR(s2.1, s2.0);
            equiv(p, (s1', pc1'), (s2', p2')) 
    {
         
    }

    lemma simul10<S>(s1: (S, nat), p: seq<(EVMProg2, seq<EVMIRProg>)>, i: EVMInst, p2: seq<EVMIRProg>, s2: (S, seq<EVMIRProg>)) 
        requires  p == toEVM(p2)
        requires  p2 == [Block(i), Block(i)]
        requires  equiv(p, (s1.0, s1.1), (s2.0, s2.1))
        ensures toEVM(p2) == [(EVMProg2.AInst(i), [Block(i), Block(i)]), (EVMProg2.AInst(i), [Block(i)])] 
        ensures 
            var (pc1', s1') := stepEVM2(s1.1, p, s1.0);
            var (s2', p2') := stepEVMIR(s2.1, s2.0);
            equiv(p, (s1', pc1'), (s2', p2')) 
    {
        // calc == {
        //     toEVM(p2);
        //     [(EVMProg2.AInst(i), p2)] + toEVM(p2[1..]);
        //     [(EVMProg2.AInst(i), p2)] + toEVM([Block(i)]);
        // }
        if s1.1 == |toEVM(p2)| {
            // var (pc1', s1') := stepEVM2(s1.1, p, s1.0);
            // assert pc1' == |toEVM(p2)|;
            // var (s2', p2') := stepEVMIR(s2.1, s2.0);
            // assume equiv(p, (s1', pc1'), (s2', p2'));
        } else {
            var (pc1', s1') := stepEVM2(s1.1, p, s1.0);
            // var (s2', p2') := stepEVMIR(s2.1, s2.0);
            // assume equiv(p, (s1', pc1'), (s2', p2'));
        }

    }

    lemma simul11<S>(s1: (S, nat), i: EVMInst, p2: seq<EVMIRProg>, s2: (S, seq<EVMIRProg>)) 
        requires  p2 == [Block(i), Block(i)]
        ensures toEVM(p2) == [(EVMProg2.AInst(i), [Block(i), Block(i)]), (EVMProg2.AInst(i), [Block(i)])] 
    {
        calc == {
            toEVM(p2);
            [(EVMProg2.AInst(i), p2)] + toEVM(p2[1..]);
            [(EVMProg2.AInst(i), p2)] + toEVM([Block(i)]);
        }
    }

    lemma simul12<S>(s1: (S, nat), c: S -> bool, i: EVMInst, p2: seq<EVMIRProg>, s2: (S, seq<EVMIRProg>)) 
        requires  p2 == [While(c, [Block(i)])]
        ensures toEVM(p2) == [
                    (EVMProg2.Jumpi(negF(c), 3), p2),
                    (EVMProg2.AInst(i), [Block(i)] + p2),
                    (EVMProg2.Jump(-2), p2)  
                ] 
    {
        var xbb := toEVM([Block(i)]);  
        assert |xbb| == |toEVM([Block(i)])| == 1;
        calc == {
            toEVM(p2);
            [(EVMProg2.Jumpi(negF(c), |xbb| + 2), p2)] +  //  0 
                        continuationClosure(xbb, p2) +            //  1..|xbb|
                    [(EVMProg2.Jump(-(|xbb| + 1)), p2)]           //  |xbb| + 1
                    +  toEVM(p2[1..]);
            [(EVMProg2.Jumpi(negF(c), 3), p2),
                (EVMProg2.AInst(i), [Block(i)] + p2),
                (EVMProg2.Jump(-2), p2)] ;
        }
    }

    // method {:verify false} display(p: seq<(EVMProg2, seq<EVMIRProg>)>) 
    // {
    //     print "here";
    //     for i := 0 to |p| - 1 {
    //         print i;
    //         match p[i].0 
    //             case AInst(i) => print(i.name);
    //             case _ => print "NOP";
    //     }
    // }

    // method {:verify false} Main() {
    //     // var i := Inst(x => x + 1, "one");
    //     // var p := toEVM([Block(i)]);
    //     // display(p);
    //     print "here";
    // }

    /**
     *  Jumps in the translated EVMIR programs are within [0, |toEVM(p)|].
     *
     *  @param  p   An EVM-IR program.
     */
    // lemma {:verify false} toEVMIsClosed(p: EVMIRProg) 
    //     ensures isClosed(toEVM(p))
    // {
    //     match p 
    //         case Block(i) => 
    //         case While(c, Block(b)) => 
    //         case IfElse(cond, Block(b1), Block(b2)) => 
    //         case While(c, xb) => 
    //             var xbb := toEVM(xb);
    //             var whileEVM :=  
    //                 [EVMProg2.Jumpi(negF(c), |xbb| + 2)] + 
    //                     xbb + 
    //                 [ EVMProg2.Jump(-(|xbb| + 1))];
    //             assert toEVM(While(c, xb)) == whileEVM;
    //             //  Prove closeness.
    //             forall (i: nat | 0 <= i < |whileEVM|) 
    //                 ensures closeJump(whileEVM, i)
    //             {
    //                 if 1 <= i < |whileEVM| - 1 {
    //                     //  Instruction i in whileEVM is intruction i - 1 xbb 
    //                     toEVMIsClosed(xb); 
    //                     match whileEVM[i] 
    //                         case Jumpi(cond, tgt) => 
    //                             //  Jump must be to an instruction between 1 and |whileEVM| - 1
    //                             calc ==> {
    //                                 //  Induction on xbb
    //                                 closeJump(xbb, i - 1);
    //                                 0 <= i - 1 + tgt <= |xbb|;
    //                                 calc == {
    //                                     |xbb|;
    //                                     |whileEVM| - 2;  
    //                                 }
    //                                 0 <= i - 1 + tgt <= |whileEVM| - 2;
    //                                 1 <= i + tgt <= |whileEVM| - 1;
    //                                 0 <= i + tgt <= |whileEVM|;
    //                             }
    //                         case Jump(tgt) => 
    //                             //  Jump must be to an instruction between 1 and |whileEVM| - 1
    //                             calc ==> {
    //                                 closeJump(xbb, i - 1);
    //                                 0 <= i - 1 + tgt <= |xbb|;
    //                                 calc == {
    //                                     |xbb|;
    //                                     |whileEVM| - 2;   
    //                                 }
    //                                 0 <= i - 1 + tgt <= |whileEVM| - 2;
    //                                 1 <= i + tgt <= |whileEVM| - 1;
    //                                 0 <= i + tgt <= |whileEVM|;
    //                             }
    //                         case _ => 
    //                 } else {
    //                     //  i == 0 or i == |whileEVM| - 1
    //                     assert closeJump(whileEVM, 0);
    //                     assert closeJump(whileEVM, |whileEVM| - 1);
    //                 }
    //             }
    //         case IfElse(cond, xb1, xb2) => 
    //             var xbb1 := toEVM(xb1);
    //             var xbb2 := toEVM(xb2);
    //             var ifElseEVM := 
    //                 [EVMProg2.Jumpi(negF(cond), |xbb1| + 2)] + //   0
    //                     xbb1 +                      //  instructions from 1 to |xbb1|
    //                 [EVMProg2.Jump(|xbb2| + 1)] +   //  instruction |xbb1| + 1
    //                     xbb2;                       //  instructions from |xbb1| + 2 to |xbb1| + |xbb2| + 1
    //             assert toEVM(IfElse(cond, xb1, xb2)) == ifElseEVM;
    //             forall (i: nat | 0 <= i < |ifElseEVM|) 
    //                 ensures closeJump(ifElseEVM, i)
    //             {
    //                 if 1 <= i <= |xbb1| {
    //                     toEVMIsClosed(xb1);
    //                     //  ifElseEVM[i] is xbb[i - 1]
    //                     match ifElseEVM[i]
    //                         case Jumpi(cond, tgt) => 
    //                              calc ==> {
    //                                 closeJump(xbb1, i - 1);
    //                                 0 <= i - 1 + tgt <= |xbb1|;
    //                                 1 <= i + tgt <= |xbb1| + 1;
    //                                 calc <= {
    //                                     |xbb1| + 1;
    //                                     |ifElseEVM|;  
    //                                 }
    //                                 0 <= i + tgt <= |ifElseEVM|; 
    //                             }
    //                         case Jump(tgt) => 
    //                             calc ==> {
    //                                 closeJump(xbb1, i - 1);
    //                                 0 <= i - 1 + tgt <= |xbb1|;
    //                                 1 <= i + tgt <= |xbb1| + 1;
    //                                 calc <= {
    //                                     |xbb1| + 1;
    //                                     |ifElseEVM|;  
    //                                 }
    //                                 0 <= i + tgt <= |ifElseEVM|; 
    //                             }
    //                         case _ => 
    //                 } else if |xbb1| + 2 <= i < |ifElseEVM| {
    //                     toEVMIsClosed(xb2);
    //                     //  ifElseEVM[i] is xbb2[i - (|xbb1| + 2)]
    //                     match ifElseEVM[i]
    //                         case Jumpi(cond, tgt) => 
    //                              calc ==> {
    //                                 closeJump(xbb2, i - (|xbb1| + 2));
    //                                 0 <= i - (|xbb1| + 2) + tgt <= |xbb2|;
    //                                 |xbb1| + 2 <= i + tgt <=  |xbb2| + (|xbb1| + 2);
    //                                 calc <= {
    //                                     |xbb2| + (|xbb1| + 2);
    //                                     |ifElseEVM|;  
    //                                 }
    //                                 0 <= i + tgt <= |ifElseEVM|; 
    //                             }
    //                         case Jump(tgt) => 
    //                             calc ==> {
    //                                 closeJump(xbb2, i - (|xbb1| + 2));
    //                                 0 <= i - (|xbb1| + 2) + tgt <= |xbb2|;
    //                                 |xbb1| + 2 <= i + tgt <=  |xbb2| + (|xbb1| + 2);
    //                                 calc <= {
    //                                     |xbb2| + (|xbb1| + 2);
    //                                     |ifElseEVM|;  
    //                                 }
    //                                 0 <= i + tgt <= |ifElseEVM|; 
    //                             }
    //                         case _ => 
    //                 } else {
    //                     assert i == 0 || i == |xbb1| + 1;
    //                     assert closeJump(ifElseEVM, i);
    //                 } 
    //             }
    // }

    

    /**
     *  General proof of simulation.
     *
     *  @returns    The (minimum) number of steps in the EVMIR to simulate n steps in EVM. 
     */
    // lemma {:verify true} foo101<S>(xb: EVMIRProg, s: S, n: nat) returns (k: nat)
    //     ensures isClosed(toEVM(xb))
    //     ensures k <= n && runEVMIR3(xb, s, k).0 == runEVM3(0, toEVM(xb), s, n).0
    // {
    //     toEVMIsClosed(xb);
    //     if n < 1 {
    //         k := 0;
    //     } else {
    //         match xb 
    //             case Block(i) => 
    //                 calc == {
    //                     runEVM2(0, toEVM(xb), s, n).0;
    //                     runEVM2(0, [EVMProg2.AInst(i)], s, n).0;
    //                     runInst(i, s);
    //                     runEVMIR3(Block(i), s, n).0;
    //                     runEVMIR3(xb, s, n).0;
    //                 }
    //                 k := n ;

    //             case While(c, xb) => 
    //                 var xbb := toEVM(xb);
    //                 var whileEVM :=  [EVMProg2.Jumpi(negF(c), |xbb| + 2)] + xbb + [ EVMProg2.Jump(-(|xbb| + 2))];
    //                 if c(s) {
    //                     if n == 1 {
    //                         k := n;
    //                     } else {
    //                         assert n >= 2;
    //                         //  do one step in toEVM(While(c, xb))
    //                         //  target state is s1 
    //                         calc == {
    //                             runEVM2(0, whileEVM, s, n);
    //                             runEVM2(1, whileEVM, s, n - 1);
    //                             // (s, |xbb| + 2);
    //                         }  
    //                         var (s', n') := runEVMIR2([xb], s, n - 1);
    //                         //  From s1, run toEVM(xb). Match with k1 steps in xb

    //                         //  first n steps of toEVM(While(c, xb)) can be simulated by 
    //                         //  1 + k1 

    //                         //  Then finish running

    //                         //  Use n - 1 steps to simulate toEVM(xb) 
    //                         var (s1, n1) := runEVM2(0, toEVM(xb), s, n - 1);       
    //                         if n1 < 2 {
    //                             k := 0;
    //                         } else {
    //                             k := 1;
    //                         }
    //                         // calc == {

    //                         // }
    //                         k := 0;
    //                         assume runEVMIR3(While(c, xb), s, k).0 == runEVM3(0, toEVM(While(c, xb)), s, n).0;
    //                     }
    //                 } else {
    //                     //  Condition is false, exit the loop and the jump program
    //                     assert negF(c)(s);
    //                     calc == {
    //                         runEVM3(0, whileEVM, s, n).0;
    //                         runEVM3(|xbb| + 1, whileEVM, s, n - 1).0;
    //                         // (s, |xbb| + 1);
    //                     }  
    //                     //  In the while program, same state is reached in 1 step.
    //                     calc == {
    //                         runEVMIR3(While(c, xb), s, n);
    //                         // runEVMIR3(, s , n - 1);
    //                         (s, n - 1);
    //                     }
    //                     k := n;
    //                 }

    //             case IfElse(c, xb1, xb2) => 
    //                 var p := toEVM(IfElse(c, xb1, xb2));
    //                     var xbb1 := toEVM(xb1);
    //                     var xbb2 := toEVM(xb2);
    //                     assert p == 
    //                         [EVMProg2.Jumpi(negF(c), |xbb1| + 2)] +  // 0 
    //                             xbb1 +                                  // 1..|xbb1|
    //                         [ EVMProg2.Jump(|xbb2| + 1)] +              //  |xbb1| + 1
    //                             xbb2;
    //                 if c(s) {
    //                     //  c(s) is true then execute xbb1
    //                     // pcBoundsOnTermination(toEVM(xb1));
    //                     //  Comopute new state and pc' and n'
    //                     var (s', pc', n') := runEVM3(0, xbb1, s, n - 1);

    //                     //  Get a simulation of xbb1 in k1 steps
    //                     var k1 := foo101(xb1, s, n - 1);
    //                     calc == {
    //                         runEVM3(0, xbb1, s, n - 1).0;
    //                         runEVMIR3(xb1, s, k1).0;
    //                     }
    //                     if pc' == |xbb1| {
    //                         //  xbb1 could be run till the end 

    //                     } else {
    //                         //  xbb1 could not be run till the end
    //                         //  p[1..|xbb1] is closed and actually equal to xbb1
    //                         calc == {   //   to finish
    //                             p[1..|xbb1|];
    //                             ([EVMProg2.Jumpi(negF(c), |xbb1| + 2)] +  
    //                                 xbb1 +                                
    //                             [ EVMProg2.Jump(|xbb2| + 1)] +            
    //                                 xbb2)[1..|xbb1|];  
    //                         }
    //                         assume p[1..|xbb1|] == xbb1;
    //                         calc == {
    //                             runEVM3(0, p, s, n);
    //                             runEVM3(1, p, s, n - 1); 
    //                             // runEVM2(0, xbb1, s, n - 1);
    //                         }
                        
    //                     // var (s', n') := runEVMIR2([xb1], s, n - 1);
    //                     // calc == {
    //                     //     runEVMIR2([IfElse(c, xb1, xb2)], s, n);
    //                     //     runEVMIR2([], s', n - 1 - n');
    //                     //     (s', n - 1 - n');
    //                     }
    //                     k := 1;
    //                     assume runEVMIR3(IfElse(c, xb1, xb2), s, k).0 == runEVM3(0, toEVM(IfElse(c, xb1, xb2)), s, n).0;

    //                 } else {
    //                     k := 1; 
    //                     //  execute xb2 
    //                     assume runEVMIR3(IfElse(c, xb1, xb2), s, k).0 == runEVM3(0, toEVM(IfElse(c, xb1, xb2)), s, n).0;

    //                 }
    //     }
    // }
        
    //  Translation proof (simple). Consistency check.

    /**
     *  Single While loop. Assume Unique block in loop body.
     *
     *  @returns    The (minimum) number of steps in the EVMIR to simulate n steps in EVM. 
     */
    // lemma {:verify false} singleWhileSim<S>(i: EVMInst, cond: S -> bool, n: nat, s: S) returns (k: nat)
    //      ensures k <= n && runEVMIR([While(cond, Block(i))], s, k) ==
    //         runEVM2(
    //             0,
    //             toEVM(While(cond, Block(i))),
    //             s, 
    //             n).0
    // {
    //     //  For convenience and clarity, store program in a var 
    //     var p :=  toEVM(While(cond, Block(i)));
    //     if n < 2 {
    //         //  Only one step can be simulated so the instruction at pc is not executed.
    //         k := 0;
    //     } else if n < 3 {
    //         //  Exactly two steps in the EVM. 
    //         assert n == 2;
    //         if cond(s) {
    //             k := 1;
    //         } else {
    //             assert !cond(s);
    //             k := 0;
    //         }
    //     } else {
    //         //  More than 2 steps in the EVM. So at least one iteration of the EVM body.
    //         assert n > 2;
    //         assert |toEVM(Block(i))| == 1;
    //         if cond(s) {
    //             calc == {
    //                 runEVM2(0, p, s, n);
    //                 runEVM2(1, p, s, n - 1);
    //                 runEVM2(2, p, runInst(i, s), n - 2);
    //                 runEVM2(0, p, runInst(i, s), n - 3);
    //             }
    //             //  Because body of while and jump progs are the same, they reach the same
    //             //  state after one iteration of the body.
    //             calc == {
    //                 runEVMIR([While(cond, Block(i))], s, n);
    //                 runEVMIR([While(cond, Block(i))], runInst(i, s), n - 1);
    //             }
    //             //  And by induction, we can get a simulation for the n - 3 remaining steps compute the same
    //             //  result.
    //             var xk := singleWhileSim(i, cond, n - 3, runInst(i, s));
    //             //  Overall we do the body of the loop once and then in xk steps simulate the rest.
    //             k := 1 + xk;
    //         } else {
    //             assert !cond(s);
    //             //  Exit the loop.
    //             k := 1;
    //         }    
    //     }
    // }    
        
    /**
     *  If Then Else Simulation proof. Assume unique block in ifBody and ifElse.
     *
     *  @returns    The (minimum) number of steps in the EVMIR to simulate n steps in EVM. 
     */
    // lemma {:verify false} ifTheElseSim<S>(i1: EVMInst, i2: EVMInst, cond: S -> bool, n: nat, s: S) returns (k: nat)
    //     requires n > 2
    //     ensures k <= n && runEVMIR([IfElse(cond, Block(i1), Block(i2))], s, k) ==  
    //         runEVM2(
    //             0,
    //             toEVM(IfElse(cond, Block(i1), Block(i2))),
    //             s, 
    //             n).0
    // { 
    //     var p := toEVM(IfElse(cond, Block(i1), Block(i2)));
    //     if n < 3 {
    //         //  if less than 1 step, only evaluate condition which takes no steps in EVM-IR
    //         if n <= 1 {
    //             k := 0 ;
    //         } else {
    //             //  Evaluate condition and execute i1 or i2. One step in EVM-IR
    //             k := 1;
    //         }
    //     } else {
    //         assert |toEVM(Block(i1))| == 1;
    //         assert |toEVM(Block(i2))| == 1; 
    //         if cond(s) {
    //             //  Execute the ifBody
    //             calc == {
    //                 runEVM2(0, p, s, n);
    //                 runEVM2(1, p, s, n - 1);
    //                 runEVM2(2, p, runInst(i1, s), n - 2);
    //                 runEVM2(4, p, runInst(i1, s), n - 3);
    //             }
    //             //  EVM-IR program simulates p in 2 steps
    //             calc == {
    //                 runEVMIR([IfElse(cond, Block(i1), Block(i2))], s, n);
    //                 runEVMIR([], runInst(i1, s), n - 1);
    //                 runInst(i1, s);
    //             }
    //             k := n - 2;
    //         } else {
    //             assert !cond(s);
    //             calc == {
    //                 runEVM2(0, p, s, n);
    //                 runEVM2(3, p, s, n - 1);
    //                 runEVM2(4, p, runInst(i2, s), n - 2);
    //             }
    //             //  EVM-IR program simulates p in 2 steps
    //             calc == {
    //                 runEVMIR([IfElse(cond, Block(i1), Block(i2))], s, n);
    //                 runEVMIR([], runInst(i2, s), n - 1);
    //                 runInst(i2, s);
    //             }
    //             k := n - 2;
    //         }
    //     }
    // }


}
