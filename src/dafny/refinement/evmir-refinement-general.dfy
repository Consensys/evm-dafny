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

    /**
     *  Translate and EVMir program into a EVM program.
     *
     *  @param  p   An EVM-IR program.
     *  @returns    Its translation into EVM (while and if are mapped to jumps).
     */
    function method toEVM<S>(p: EVMIRProg): seq<EVMProg2> 
    {
        match p 
            case Block(i) => [EVMProg2.AInst(i)]
            // case While(c, Block(b)) => 
            //     [
            //         EVMProg2.Jumpi(negF(c), 3),     // 0
            //         EVMProg2.AInst(b),              // 1
            //         EVMProg2.Jump(-2)               // 2
            //     ]
            // case IfElse(cond, Block(b1), Block(b2)) => 
            //     [
            //         EVMProg2.Jumpi(negF(cond), 3),  // 0
            //         EVMProg2.AInst(b1),             // 1
            //         EVMProg2.Jump(2),               // 2
            //         EVMProg2.AInst(b2)              // 3
            //     ]
            //  
            case While(c, xb) => 
                //   Translate xb into EVM. xbb goes from 0 to |xbb| - 1
                var xbb := toEVM(xb);
                //  transaliton of While is 0 -> jumpi, 1..|xbb| xbb, xbb + 1 -> Jump
                [EVMProg2.Jumpi(negF(c), |xbb| + 2)] + xbb + [ EVMProg2.Jump(-(|xbb| + 1))]
            case IfElse(cond, xb1, xb2) => 
                var xbb1 := toEVM(xb1);
                var xbb2 := toEVM(xb2);
                [EVMProg2.Jumpi(negF(cond), |xbb1| + 1)] + 
                    xbb1 + 
                [ EVMProg2.Jump(|xbb2| + 1)] +
                    xbb2

                // [
                //     EVMProg2.Jumpi(negF(cond), 3),  // 0
                //     EVMProg2.AInst(b1),             // 1
                //     EVMProg2.Jump(2),               // 2
                //     EVMProg2.AInst(b2)              // 3
                // ]
            // case _ => //  Cases not covered
            //     []
    }

    /**
     *  Jumps in the translated EVMIR programs are within [0, |toEVM(p)|].
     *
     *  @param  p   An EVM-IR program.
     */
    lemma toEVMIsClosed(p: EVMIRProg) 
        ensures isClosed(toEVM(p))
    {
        match p 
            case Block(i) => 
            case While(c, Block(b)) => 
            case IfElse(cond, Block(b1), Block(b2)) => 
            case While(c, xb) => 
                var xbb := toEVM(xb);
                var whileEVM :=  
                    [EVMProg2.Jumpi(negF(c), |xbb| + 2)] + 
                        xbb + 
                    [ EVMProg2.Jump(-(|xbb| + 1))];
                assert toEVM(While(c, xb)) == whileEVM;
                //  Prove closeness.
                forall (i: nat | 0 <= i < |whileEVM|) 
                    ensures closeJump(whileEVM, i)
                {
                    if 1 <= i < |whileEVM| - 1 {
                        //  Instruction i in whileEVM is intruction i - 1 xbb 
                        toEVMIsClosed(xb); 
                        match whileEVM[i] 
                            case Jumpi(cond, tgt) => 
                                //  Jump must be to an instruction between 1 and |whileEVM| - 1
                                calc ==> {
                                    //  Induction on xbb
                                    closeJump(xbb, i - 1);
                                    0 <= i - 1 + tgt <= |xbb|;
                                    calc == {
                                        |xbb|;
                                        |whileEVM| - 2;  
                                    }
                                    0 <= i - 1 + tgt <= |whileEVM| - 2;
                                    1 <= i + tgt <= |whileEVM| - 1;
                                    0 <= i + tgt <= |whileEVM|;
                                }
                            case Jump(tgt) => 
                                //  Jump must be to an instruction between 1 and |whileEVM| - 1
                                calc ==> {
                                    closeJump(xbb, i - 1);
                                    0 <= i - 1 + tgt <= |xbb|;
                                    calc == {
                                        |xbb|;
                                        |whileEVM| - 2;   
                                    }
                                    0 <= i - 1 + tgt <= |whileEVM| - 2;
                                    1 <= i + tgt <= |whileEVM| - 1;
                                    0 <= i + tgt <= |whileEVM|;
                                }
                            case _ => 
                    } else {
                        //  i == 0 or i == |whileEVM| - 1
                        assert closeJump(whileEVM, 0);
                        assert closeJump(whileEVM, |whileEVM| - 1);
                    }
                }
            case IfElse(cond, xb1, xb2) => 
                var xbb1 := toEVM(xb1);
                var xbb2 := toEVM(xb2);
                var ifElseEVM := [EVMProg2.Jumpi(negF(cond), |xbb1| + 1)] + 
                    xbb1 +                      //  instructions from 1 to |xbb1|
                [ EVMProg2.Jump(|xbb2| + 1)] +  //  instruction |xbb1| + 1
                    xbb2;                       //  instructions from |xbb1| + 2 to |xbb1| + 2 + |xbb2|
                assert toEVM(IfElse(cond, xb1, xb2)) == ifElseEVM;
                forall (i: nat | 0 <= i < |ifElseEVM|) 
                    ensures closeJump(ifElseEVM, i)
                {
                    if 1 <= i <= |xbb1| {
                        toEVMIsClosed(xb1);
                        //  ifElseEVM[i] is xbb[i - 1]
                        match ifElseEVM[i]
                            case Jumpi(cond, tgt) => 
                                 calc ==> {
                                    closeJump(xbb1, i - 1);
                                    0 <= i - 1 + tgt <= |xbb1|;
                                    1 <= i + tgt <= |xbb1| + 1;
                                    calc <= {
                                        |xbb1| + 1;
                                        |ifElseEVM|;  
                                    }
                                    0 <= i + tgt <= |ifElseEVM|; 
                                }
                            case Jump(tgt) => 
                                calc ==> {
                                    closeJump(xbb1, i - 1);
                                    0 <= i - 1 + tgt <= |xbb1|;
                                    1 <= i + tgt <= |xbb1| + 1;
                                    calc <= {
                                        |xbb1| + 1;
                                        |ifElseEVM|;  
                                    }
                                    0 <= i + tgt <= |ifElseEVM|; 
                                }
                            case _ => 
                    } else if |xbb1| + 2 <= i < |ifElseEVM| {
                        toEVMIsClosed(xb2);
                        //  ifElseEVM[i] is xbb2[i - (|xbb1| + 2)]
                        match ifElseEVM[i]
                            case Jumpi(cond, tgt) => 
                                 calc ==> {
                                    closeJump(xbb2, i - (|xbb1| + 2));
                                    0 <= i - (|xbb1| + 2) + tgt <= |xbb2|;
                                    |xbb1| + 2 <= i + tgt <=  |xbb2| + (|xbb1| + 2);
                                    calc <= {
                                        |xbb2| + (|xbb1| + 2);
                                        |ifElseEVM|;  
                                    }
                                    0 <= i + tgt <= |ifElseEVM|; 
                                }
                            case Jump(tgt) => 
                                calc ==> {
                                    closeJump(xbb2, i - (|xbb1| + 2));
                                    0 <= i - (|xbb1| + 2) + tgt <= |xbb2|;
                                    |xbb1| + 2 <= i + tgt <=  |xbb2| + (|xbb1| + 2);
                                    calc <= {
                                        |xbb2| + (|xbb1| + 2);
                                        |ifElseEVM|;  
                                    }
                                    0 <= i + tgt <= |ifElseEVM|; 
                                }
                            case _ => 
                    } else {
                        assert i == 0 || i == |xbb1| + 1;
                        assert closeJump(ifElseEVM, i);
                    } 
                }
    }

    // lemma foo303()

    /**
     *  Single While loop. Assume Unique block in loop body.
     *
     *  @returns    The (minimum) number of steps in the EVMIR to simulate n steps in EVM. 
     */
    lemma {:verify false} foo101<S>(xb: EVMIRProg, n: nat, s: S) returns (k: nat)
        // requires n > 1
        // requires n < 3
        ensures k <= n && runEVMIR2([xb], s, k).0 == runEVM2(0, toEVM(xb), s, n).0
    {
        if n < 1 {
            k := 0;
        } else {
            match xb 
                case Block(i) => 
                    calc == {
                        runEVM2(0, toEVM(xb), s, n).0;
                        runEVM2(0, [EVMProg2.AInst(i)], s, n).0;
                        runInst(i, s);
                        runEVMIR2([Block(i)], s, n).0;
                        runEVMIR2([xb], s, n).0;
                    }
                    k := n ;
                case While(c, xb) => 
                    var xbb := toEVM(xb);
                    var whileEVM :=  [EVMProg2.Jumpi(negF(c), |xbb| + 2)] + xbb + [ EVMProg2.Jump(-(|xbb| + 2))];
                    if c(s) {
                        if n == 1 {
                            k := n;
                        } else {
                            assert n >= 2;
                            //  do one step in toEVM(While(c, xb))
                            //  target state is s1 
                            calc == {
                                runEVM2(0, whileEVM, s, n);
                                runEVM2(1, whileEVM, s, n - 1);
                                // (s, |xbb| + 2);
                            }  
                            var (s', n') := runEVMIR2([xb], s, n - 1);
                            //  From s1, run toEVM(xb). Match with k1 steps in xb

                            //  first n steps of toEVM(While(c, xb)) can be simulated by 
                            //  1 + k1 

                            //  Then finish running

                            //  Use n - 1 steps to simulate toEVM(xb) 
                            var (s1, n1) := runEVM2(0, toEVM(xb), s, n - 1);       
                            if n1 < 2 {
                                k := 0;
                            } else {
                                k := 1;
                            }
                            // calc == {

                            // }
                            k := 0;
                            assume runEVMIR2([While(c, xb)], s, k).0 == runEVM2(0, toEVM(While(c, xb)), s, n).0;
                        }
                    } else {
                        //  Condition is false, exit the loop and the jump program
                        assert negF(c)(s);
                        calc == {
                            runEVM2(0, whileEVM, s, n);
                            runEVM2(|xbb| + 2, whileEVM, s, n - 1);
                            (s, |xbb| + 2);
                        }  
                        //  In the while program, same state is reached in 1 step.
                        calc == {
                            runEVMIR2([While(c, xb)], s, n);
                            runEVMIR2([While(c, xb)][1..], s , n - 1);
                            (s, n - 1);
                        }
                        k := n;
                    }
                case IfElse(c, xb1, xb2)=> 
                    k := 0;
                    assume runEVMIR2([IfElse(c, xb1, xb2)], s, k).0 == runEVM2(0, toEVM(IfElse(c, xb1, xb2)), s, n).0;
        }
    }
        
    //  Translation proof (simple)
    /**
     *  Single While loop. Assume Unique block in loop body.
     *
     *  @returns    The (minimum) number of steps in the EVMIR to simulate n steps in EVM. 
     */
    lemma {:verify false} singleWhileSim<S>(i: EVMInst, cond: S -> bool, n: nat, s: S) returns (k: nat)
         ensures k <= n && runEVMIR([While(cond, Block(i))], s, k) ==
            runEVM2(
                0,
                toEVM(While(cond, Block(i))),
                s, 
                n).0
    {
        //  For convenience and clarity, store program in a var 
        var p :=  toEVM(While(cond, Block(i)));
        if n < 2 {
            //  Only one step can be simulated so the instruction at pc is not executed.
            k := 0;
        } else if n < 3 {
            //  Exactly two steps in the EVM. 
            assert n == 2;
            if cond(s) {
                k := 1;
            } else {
                assert !cond(s);
                k := 0;
            }
        } else {
            //  More than 2 steps in the EVM. So at least one iteration of the EVM body.
            assert n > 2;
            if cond(s) {
                calc == {
                    runEVM2(0, p, s, n);
                    runEVM2(1, p, s, n - 1);
                    runEVM2(2, p, runInst(i, s), n - 2);
                    runEVM2(0, p, runInst(i, s), n - 3);
                }
                //  Because body of while and jump progs are the same, they reach the same
                //  state after one iteration of the body.
                calc == {
                    runEVMIR([While(cond, Block(i))], s, n);
                    runEVMIR([While(cond, Block(i))], runInst(i, s), n - 1);
                }
                //  And by induction, we can get a simulation for the n - 3 remaining steps compute the same
                //  result.
                var xk := singleWhileSim(i, cond, n - 3, runInst(i, s));
                //  Overall we do the body of the loop once and then in xk steps simulate the rest.
                k := 1 + xk;
            } else {
                //  Exit the loop.
                assert !cond(s);
                k := 1;
            }    
        }
    }    
        
    /**
     *  If Then Else Simulation proof. Assume unique block in ifBody and ifElse.
     *
     *  @returns    The (minimum) number of steps in the EVMIR to simulate n steps in EVM. 
     */
    lemma {:verify false} ifTheElseSim<S>(i1: EVMInst, i2: EVMInst, cond: S -> bool, n: nat, s: S) returns (k: nat)
        requires n > 2
        ensures k <= n && runEVMIR([IfElse(cond, Block(i1), Block(i2))], s, k) ==  
            runEVM2(
                0,
                toEVM(IfElse(cond, Block(i1), Block(i2))),
                s, 
                n).0
    { 
        var p := toEVM(IfElse(cond, Block(i1), Block(i2)));
        if n < 3 {
            //  if less than 1 step, only evaluate condition which takes no steps in EVM-IR
            if n <= 1 {
                k := 0 ;
            } else {
                //  Evaluate condition and execute i1 or i2. One step in EVM-IR
                k := 1;
            }
        } else {
            if cond(s) {
                //  Execute the ifBody
                calc == {
                    runEVM2(0, p, s, n);
                    runEVM2(1, p, s, n - 1);
                    runEVM2(2, p, runInst(i1, s), n - 2);
                    runEVM2(4, p, runInst(i1, s), n - 3);
                }
                //  EVM-IR program simulates p in 2 steps
                calc == {
                    runEVMIR([IfElse(cond, Block(i1), Block(i2))], s, n);
                    runEVMIR([], runInst(i1, s), n - 1);
                    runInst(i1, s);
                }
                k := n - 2;
            } else {
                assert !cond(s);
                calc == {
                    runEVM2(0, p, s, n);
                    runEVM2(3, p, s, n - 1);
                    runEVM2(4, p, runInst(i2, s), n - 2);
                }
                //  EVM-IR program simulates p in 2 steps
                calc == {
                    runEVMIR([IfElse(cond, Block(i1), Block(i2))], s, n);
                    runEVMIR([], runInst(i2, s), n - 1);
                    runInst(i2, s);
                }
                k := n - 2;
            }
        }
    }


}
