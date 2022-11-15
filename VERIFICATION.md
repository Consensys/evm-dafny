

# Table of Contents

1. [Bytecode verification](#verifying-bytecode)
   1. [Overflow Checker for ADD](#an-overflow-checker)
        1. [Detecting Overflows in ADD](#detecting-overflows)
        1. [Formal Verification of the Overflow Checker](#formally-verifying-the-overflow-checker)
        1. [Results](#results-of-the-verification)

# Verifying Bytecode

## An Overflow Checker

### The code and the objective

The example below is a code snippet in [this example file](src/test/dafny/FM-paper.dfy).

First some bytecode is created using the `Code.Create` function from [the EVM abstract module](src/dafny/evm.dfy).
```dafny
/** Code snippet that detects overflow in addition. */
const OVERFLOW_CHECK := Code.Create(
    [   
    // 0x00  0x01           //  stack 
       DUP2, ADD,           //  [y + x, y] .    
    // 0x02   0x03  
       LT,                  //  [x + y < y?1:0] 
    // 0x03   
       PUSH1, 0x07, JUMPI,  //  [0x07, x < x + y?1:0] 
    // If Peek(1) is 0 no overflow, STOP, otherwise JUMP and revert.
    // 0x06
       STOP,   
    // 0x07      0x08   0x09  0x10   0x11, 0x12 
       JUMPDEST, PUSH1, 0x00, PUSH1, 0x00, REVERT 
    ]
    );
```

The bytecode is in the form of opcodes defined in the [Opcodes module](src/dafny/opcodes.dfy).
The more friendly layout of the code is:

```assembly
-------------------
Address|Instruction
-------------------
0x00:   DUP2
0x01:   ADD
0x02:   LT
0x03:   PUSH1 0x07
0x05:   JUMPI
0x06:   STOP
0x07:   JUMPDEST
0x08:   PUSH1 0x00
0x10:   PUSH1 0x00
0x12:   REVERT
```

The intention is that this code snippet:

- adds the two values at the top of the stack,
- detects under/overflow,
- normally terminates if no overflow happens and reverts otherwise.

What we are going to do is write a Dafny program that **verifies** that this code snippet does the job,
**for all possible inputs at the top of stack**.

### Detecting Overflows

Detecting overflows in addition modulo a given number can be done by first computing the result if an addition, and checking a property of the result against one of the inputs.
In other words, there is a necessary and sufficient condition to detect overflows on addition.
This is formally defined in the following Dafny lemma:

```dafny
/** Necessary and sufficient  condition for detecting overflow in ADD. */
lemma AddOverflowNSC(x: u256, y: u256) 
ensures  /* C1 */ x as nat + y as nat > MAX_U256
    <==> /* C2 */ (x as nat + y as nat) % TWO_256 < x as nat 
{
   //  Proof should be here, but Dafny can prove it on its own. Thanks Dafny!
}
```
This lemma asserts (postcondition `ensures`) that the following conditions are equivalent (`<==>`):
- C1: the sum of `x` and `y` _as if there were natural numbers_ is larger than `MAX_U256 = 2^256 - 1`,
- C2: the sum of `x` and `y` _modulo_ `2^256` is less than `x` (`y` would work too as the `+` is symmetric).

Dafny successfully verifies this lemma, using clever **automated reasoning** and an SMT-solver in the backend.
What we end up with is _machine-checkable proof_ (by Dafny) that the lemma is valid (for all inputs `x` and `y` of type `u256`).
We can now use this fact to write an overflow checker and this exaclty what  the `OVERFLOW_CHECK` code snippet does. 

### Formally Verifying the Overflow Checker
In order to verify that the overflow checker is _correct_ we need a few things:
1. a _formal specification_ of what the correctness property is
2. a _mechanism_ to run and reason about code.

To do so we are going to write a Dafmy program, a method, `OverflowCheck` that captures the specification and the correctness criteria:

- **the inputs** `x` and `y`:  there are input parameters of `OverflowCheck` together with a state `st:State` of an EVM. The inputs are arbitrary but we add some reasonable contraints on them defined by preconditions (`requires`). 
    - `Pre0` indicates that we start in a non-failure state, with the Program Counter `PC` pointing to instruction at address `0x00`.
    - `Pre1`: we assume the amount of _gas` in the EVM is larger than a certain amount. The values used here are defined for the Berlin version of the EVM semantics and available in [the Gas module](src/dafny/gas.dfy).
    - `Pre2`: the current stack contains the two values `x` and `y` with `x` at the top. But `x` and `y` are **arbitrary values** of type `u256`.
    - `Pre3`: the code that is currently executed is the `OVERFLOW_CHECK` code above.
- **the correctness criteria**: this is captured by _postconditions_ (`ensures` in Dafny). The postconditions _formally_ and _logically_ define our correctness criteria:
    - `Post0`: the code **always** terminates and the final state is either a normal stop or a revert. This excludes `out-of-gas` exception (we intend to provide enough gas in `Pre1` to ensure this postcondition).
    - `Post1`: the final state is a revert **if and only if** an overflow occurs. Note that overflow is defined mathematically with unbounded natural numbers (`nat`).
    - `Post2`: the final state ifs a normal state  **if and only if** no overflow occurs. Note that postcondition logically follows from `Post0` and `Post1`.
- **the instrumented code**: to _run_ the code we use the `ExecuteN(s, k)` function in [the EVM abstract module](src/dafny/evm.dfy). This function executes (at most) `k` steps of the code in `s`. If an invalid state (e.g. stack under/overflow, out-of-gas) is encountered before the `k`-th step the execution prematurely stops and returns the invalid state. The body of the method `OverflowCheck` below somehow _monitors_ what the bytecode is doing. If executes the first 4 instructions, resulting
in state `st'`. Depending on the result (second element of the stack `st'.Peek(1)`) of the comparison operator `LT` (semantics in [the bytecode module](src/dafny/bytecode.dfy)) what is left to execute next differs: either one instruction `STOP` or the section of the code that reverts. 
The instrumentation of the execution of the bytecode with a Dafny `if-then-else` statement enables to track this two different paths. 



```dafny
/**
 *  This is a pattern that is frequently used to detect overflows for ADD.
 *
 *  @param  st  A state.
 *  @param  x   A u256.
 *  @param  y   A u256.
 *  @returns    A normal state with `x + y` top of stack if no overflow, a 
 *              revert state otherwise..
 *  @note       The check relies on the property specified by lemma AddOverflowNSC.
 *  @note       The overflow is specified as x + y exceeding MAX_U256.
 */
method OverflowCheck(st: State, x: u256, y: u256) returns (st': State)
    /** OK state and initial PC.  */
    requires /* Pre0 */ st.OK? && st.PC() == 0 
    /** Enough gas. Longest path gas-wise is via JUMPI. */
    requires /* Pre1 */ st.Gas() >= 6 * Gas.G_VERYLOW + Gas.G_HIGH + Gas.G_JUMPDEST
    /** Initial stack is [x, y]. */
    requires /* Pre2 */ st.GetStack() == Stack.Make([x, y]);
    /** The code is the snippet to detect overflow. */
    requires /* Pre3 */ st.evm.code == OVERFLOW_CHECK
    /** The contract never runs out of gas thanls to Pre1. */
    ensures /* Post0 */ st'.REVERTS? || st'.RETURNS?
    /** Should revert iff overflow. */
    ensures /* Post1 */ st'.REVERTS? <==> x as nat + y as nat > MAX_U256
    /** Normal termination iff no overflow. */
    ensures /* Post2 */ st'.RETURNS? <==> x as nat + y as nat <= MAX_U256
{
    //  Execute 4 steps -- DUP2 ADD LT PUSH1 0x07
    st' := ExecuteN(st,4);
    //  Depending on result of LT comparison overflow or not
    if st'.Peek(1) == 0 { 
        st':= Execute(st');
        assert st'.PC() == 0x06; 
        st' := ExecuteN(st',1);
        assert st'.RETURNS?;
    } else {
        st':= Execute(st');
        assert st'.PC() == 0x07;
        st' := ExecuteN(st',4);
        assert st'.REVERTS?;
    }
}
```

So the question is now: **How does the verification work and what does it verify?**

_What_ is verified is the following _correctness property_: assuming the preconditions hold initially, 
- the body always terminates (as there is no loop this check is easy),  
- the `assert` statements are never violated, and 
- when the body of the method `OverflowCheck` terminates, the `ensures` statement hold.

As for the _How_, there several things that happen during this verification phase under the hood. In a nutshell, Dafny builds big _verification conditions_ (logical predicates), and it turns out that they are valid **if and only if** the correctness property above is true. 
Whether the verification conditions ate valid is outsourced to a backend _SMT-solver_ (Z3).

### Results of the Verification

If we check the method `OverflowCheck`, the Dafny verifier indeed confirms that it is _correct_.
So what have we proved with this process:  

- first, we have proved correctness **for all inputs**. It is a symbolic and logical reasoning process, not a _testing_ process. This is equivalent to exhaustively testing all inputs (and there are more than `2^257` possible inputs).
- second, with `Post0` we have a guarantee that the code snippet never runs out of gas. Of course this is provided with enough gas initially, as per `Pre1` which gives us a lower bound on what is needed to avoid an out-of-gas exception.
- third, we have proved that no exceptions related to stack under/overflow occur: otherwise we would 
reach an `INVALID` state which is ruled out by `Post0` 
- finaly, we have proved that the code snippet correctly detects overflows in addition (`Post1` and `Post2`).

