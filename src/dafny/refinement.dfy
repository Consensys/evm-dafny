
include "NativeTypes.dfy"
include "NonNativeTypes.dfy"

import opened NativeTypes
import opened NonNativeTypes

/**
 */

// datatype ins = Assign(to: string, v: uint256)

/** Basic instruction in EVM. Termninating. */
datatype EVMInst<!S> = 
    Inst(i : S -> S)

/** Programs with while loops/WhileNs . */
datatype EVMIR<!S> = 
    |   While(cond: S -> bool, body: EVMInst)
    |   WhileN(cond: S -> bool, body: EVMInst)
    |   Jumpi(cond: S -> bool, body: EVMInst)
    |   Jump(t: string) 


/**
 *  Compute next state.
 *  @param  i   An instruction.
 *  @param  s   A state.
 *  @result     The state reached after executing `i` from `s`.
 */
function runInst<S>(i: EVMInst<S>, s: S): S
{
    match i 
        case Inst(e) => e(s)
}

/**
 *  Run n steps of the program.
 *  @param  p   A program.
 *  @param  s   A state.
 *  @param  n   The number of steps to execute.
 *  @returns    The state obtained after executing `n` steps of `p`. 
 */
function runEVM<S>(p: seq<EVMIR>, m: map<string, EVMIR>, s: S, n: nat): S 
    decreases n - 1
{   
    if n == 0 || p == [] then s 
        //  max number of steps reached or program has terminated. 
    else 
        match p[0] 
            case While(c, b) => 
                //  if c(s)  run the body and run loop on new state.
                if c(s) then runEVM(p, m, runInst(b, s) , n - 1)
                else s
            case WhileN(c, b) =>  
                //  if !c(s) run the body and then the WhileN again.
                if !c(s) then runEVM(p, m, runInst(b, s) , n - 1)
                else s
            case Jumpi(c, b) =>  
                //  if !c(s) run the body and then the WhileN again.
                if !c(s) then runEVM(p, m, runInst(b, s) , n - 1)
                else s
            case Jump(p) => 
                //  run p from s 
                assume p in m;
                runEVM([m[p]], m, s , n - 1)
}

/**
 *  Negation of a boolean function.
 *  @param  f   A boolean function.
 *  @return     not(f) i.e. negF(x) = !f(x).
 */
function negF<S>(f: S -> bool): S -> bool { x => !f(x) }

/**
 *  Translation proof.
 *  Assume two programs, a loop 
 */
lemma foo101<S>(p1: seq<EVMIR>, p2: seq<EVMIR>, m: map<string, EVMIR>, n: nat, s: S)
    requires |p2| == 1 && |p1| > 1 
    requires p1[0].WhileN? 
    requires p2[0].While?
    requires p1[0].cond == negF(p2[0].cond)
    requires p1[0].body == p2[0].body
    ensures runEVM(p1, m, s, n) == runEVM(p2, m, s, n)
 {
    if n == 0 {
        //  Thanks Dafny
    } else if p2[0].cond(s) {
        assert !p1[0].cond(s);
        var b2 := p2[0].body;
        var b1 := p1[0].body;
        calc == {
            runEVM(p2, m, s, n);
            runEVM(p2, m, runInst(b2, s) , n - 1);
            calc == {
                runInst(b2, s);
                runInst(b1, s);
            }
            runEVM(p2, m, runInst(b1, s) , n - 1);
            { foo101(p1, p2, m, n - 1, runInst(b1, s));}
            runEVM(p1, m, runInst(b1, s) , n - 1);
            runEVM(p1, m, s, n);
        }
    } else {
        //  Thanks Dafny
    }  
 }

/**
 *  Translation proof.
 *  Assume two programs, a loop 
 *
 *  while(c, b)
 *  jumpi(!c, [b, jump[]])
 *
 */
// lemma foo202<S>(p1: seq<EVMIR>, p2: seq<EVMIR>, n: nat, s: S)
//     requires |p2| == 1 && |p1| > 1 
//     requires p1[0].WhileN? 
//     requires p2[0].While?
//     requires p1[0].cond == negF(p2[0].cond)
//     requires p1[0].body == p2[0].body
//     ensures runEVM(p1, s, n) == runEVM(p2, s, n)
//  {
//     if n == 0 {
//         //  Thanks Dafny
//     } else if p2[0].cond(s) {
//         assert !p1[0].cond(s);
//         var b2 := p2[0].body;
//         var b1 := p1[0].body;
//         calc == {
//             runEVM(p2, s, n);
//             runEVM(p2, runInst(b2, s) , n - 1);
//             calc == {
//                 runInst(b2, s);
//                 runInst(b1, s);
//             }
//             runEVM(p2, runInst(b1, s) , n - 1); 
//             { foo101(p1, p2, n - 1, runInst(b1, s));}
//             runEVM(p1, runInst(b1, s) , n - 1);
//             runEVM(p1, s, n);
//         }
//     } else {
//         //  Thanks Dafny
//     }  
//  }

