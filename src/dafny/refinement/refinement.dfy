
include "../utils/NativeTypes.dfy"
include "../utils/NonNativeTypes.dfy"

import opened NativeTypes
import opened NonNativeTypes

/** Basic instruction in EVM. Termninating. */
datatype EVMInst<!S> = 
    Inst(i : S -> S)

/** Programs with while loops/WhileNs . */
datatype EVMIR<!S> = 
    |   While(cond: S -> bool, body: EVMInst)
    |   WhileN(cond: S -> bool, body: EVMInst)

datatype EVM<!S> = 
        AInst(i: EVMInst)
    |   Jumpi(cond: S -> bool, tgt: nat)
    |   Jump(tgt: nat)


/**
 *  Compute next state.
 *  @param  i   An instruction.
 *  @param  s   A state.
 *  @result     The state reached after executing `i` from `s`.
 */
function method runInst<S>(i: EVMInst<S>, s: S): S
{
    match i 
        case Inst(e) => 
            e(s)
}

/**
 *  Semantics of EVM programs.
 */
function method runEVM<S>(pc: nat, p: map<nat, EVM>, s: S, n: nat): (S, nat)
    decreases n 
{
    if pc == 0 || n == 0 || pc !in p then (s, 0)
        //  We could have different types of termination
    else 
        //  Execute instruction at PC 
        match p[pc] 
            case AInst(Inst(i)) => 
                runEVM(pc + 1, p, i(s), n - 1)
            case Jumpi(c, tgt) => 
                if !c(s) then runEVM(pc + 1, p, s, n - 1) else runEVM(tgt, p, s, n - 1)
            case Jump(tgt) => 
                runEVM(tgt, p, s, n - 1) 
}


/**
 *  Run n steps of the program.
 *  @param  p   A program.
 *  @param  s   A state.
 *  @param  n   The number of steps to execute.
 *  @returns    The state obtained after executing `n` steps of `p`. 
 */
function method runEVMIR<S>(p: seq<EVMIR>, s: S, n: nat): S 
    decreases n - 1
{   
    if n == 0 || p == [] then s 
        //  max number of steps reached or program has terminated. 
    else 
        match p[0] 
            case While(c, b) => 
                //  if c(s)  run the body and run loop on new state.
                if c(s) then runEVMIR(p, runInst(b, s) , n - 1)
                else s
            case WhileN(c, b) =>  
                //  if !c(s) run the body and then the WhileN again.
                if !c(s) then runEVMIR(p, runInst(b, s) , n - 1)
                else s
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
lemma foo101<S>(p1: seq<EVMIR>, p2: seq<EVMIR>, n: nat, s: S)
    requires |p2| == 1 && |p1| > 1 
    requires p1[0].WhileN? 
    requires p2[0].While?
    requires p1[0].cond == negF(p2[0].cond)
    requires p1[0].body == p2[0].body
    ensures runEVMIR(p1, s, n) == runEVMIR(p2, s, n)
 {
    if n == 0 {
        //  Thanks Dafny
    } else if p2[0].cond(s) {
        assert !p1[0].cond(s);
        var b2 := p2[0].body;
        var b1 := p1[0].body;
        calc == {
            runEVMIR(p2, s, n);
            runEVMIR(p2, runInst(b2, s) , n - 1);
            calc == {
                runInst(b2, s);
                runInst(b1, s);
            }
            runEVMIR(p2, runInst(b1, s) , n - 1);
            { foo101(p1, p2, n - 1, runInst(b1, s));}
            runEVMIR(p1, runInst(b1, s) , n - 1);
            runEVMIR(p1, s, n);
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
lemma foo202<S>(i: EVMInst, cond: S -> bool, n: nat, s: S)
    ensures runEVMIR([While(cond, i)], s, n) ==
        runEVM(
            1,
            map[
                1 := Jumpi(negF(cond), 0),
                2 := AInst(i),
                3 := Jump(1)
            ], 
            s, 
            3 * n).0
{
    if n == 0 {
        //  
    } else if cond(s) {
        var p := map[
                    1 := Jumpi(negF(cond), 0),
                    2 := AInst(i),
                    3 := Jump(1)
                ];

        calc == {
            runEVM(1, p, s, 3 * n);
            { assert 1 in p; assert !negF(cond)(s); }
            runEVM(1 + 1, p, s, 3 * n - 1);
            runEVM(2, p, s, 3 * n - 1);

            runEVM(3, p, runInst(i, s), 3 * n - 2 );
            runEVM(1, p, runInst(i, s), 3 * n - 3);
            runEVM(1, p, runInst(i, s), 3 * (n - 1));
        }
        calc == {
            runEVMIR([While(cond, i)], s, n);
            runEVMIR([While(cond, i)], runInst(i, s) , n - 1);
        }
        foo202(i, cond, n - 1, runInst(i, s));
    } else {
        assert !cond(s);
    }
}
 

//  Tests

datatype S1 = S1(k: nat)

function method add(x: S1): S1 
{
    S1(x.k + 1)
}

function method test(s: S1): bool
{
    s.k <= 16
}

method Main() 
{
    //  Run a simple EVM program 
    var p1 := map[
        1 := AInst(Inst(add))
    ];

    var s0 := S1(14);
    var s1:= runEVM(1, p1, s0, 1);
    print s1, "\n";

    //  run p2 - a while loop
    s0 := S1(0);
    var p2 := While( (x:S1) => x.k < 7, Inst((x:S1) => S1(x.k + 1)));
    var r2 := runEVMIR([p2], s0, 20);
    print r2, "\n";

    //  Program with jumps to simulate p2 
    var p3 := map[
        1 := Jumpi((x:S1) => x.k > 7, 0),
        2 := AInst(Inst(add)),
        3 := Jump(1)
    ];

    var r3 := runEVM(1, p3, s0, 20);
    print r3, "\n";

}


