

# Table of Contents

1. [Bytecode verification](#verifying-bytecode)
   1. [Overflow Checker for ADD](#an-overflow-checker)
        1. [Detecting Overflows in ADD](#detecting-overflows)
        1. [Formal Verification of the Overflow Checker](#formally-verifying-the-overflow-checker)
        1. [Results](#results-of-the-verification)
   1. [Simple Loop](#a-loop-program)
        1. [Bytecode overview](#what-this-bytecode-is-doing)
        1. [Formal verification of the loop program](#formal-verification-of-the-loop-program)
        1. [Results](#results)

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
What we end up with is _machine-checkable proof_ (the lemmna is written as a program, and the program is verified by Dafny) that the lemma is valid (for all inputs `x` and `y` of type `u256`).
We can now use this fact to write an overflow checker and this exactly what  the `OVERFLOW_CHECK` code snippet does. 

### Formally Verifying the Overflow Checker
In order to verify that the overflow checker is _correct_ we need a few things:
1. a _formal specification_ of what the correctness property is
2. a mechanism to _reason_ about code.

To do so we are going to write a Dafny program (method), `OverflowCheck` (below) that captures the specification and the correctness criteria:

- **the inputs** `x` and `y`:  there are input parameters of `OverflowCheck` together with a state `st:State` of an EVM. The inputs are arbitrary but we add some reasonable contraints on them defined by preconditions (`requires`):
    - `Pre0` indicates that we start in a non-failure state, with the Program Counter `PC` pointing to instruction at address `0x00`.
    - `Pre1`: we assume the amount of `gas` in the EVM is larger than a certain amount. The values used here are defined for the Berlin version of the EVM semantics and available in [the Gas module](src/dafny/gas.dfy).
    - `Pre2`: the initial stack contains the two values `x` and `y` with `x` at the top. But `x` and `y` are **arbitrary values** of type `u256`.
    - `Pre3`: the code that is currently executed is the `OVERFLOW_CHECK` code above.
- **the correctness criteria**: this is captured by _postconditions_ (`ensures` in Dafny). The postconditions _formally_ and _logically_ define our correctness criteria:
    - the body **always** terminates; this is enforced by Dafny and when the body terminates, the following postconditions hold:
    - `Post0`: the final state is either a normal stop or a revert. This excludes `out-of-gas` exception (we intend to provide enough gas in `Pre1` to ensure this postcondition).
    - `Post1`: the final state is a revert **if and only if** an overflow occurs. Note that overflow is defined mathematically with unbounded natural numbers (`nat`).
    - `Post2`: the final state is a normal state  **if and only if** no overflow occurs. That postcondition logically follows from `Post0` and `Post1`.
- **the instrumented code**: to _run_ the code we use the `ExecuteN(s, k)` function in [the EVM abstract module](src/dafny/evm.dfy). This function executes (at most) `k` steps of the code in `s`. If an invalid state (e.g. stack under/overflow, out-of-gas) is encountered before the `k`-th step the execution prematurely stops and returns the invalid state. The body of the method `OverflowCheck` below somehow _monitors_ what the bytecode is doing. If executes the first 4 instructions, resulting
in state `st' == ExecuteN(st, 4)`. Depending on the result (second element of the stack `st'.Peek(1)`) of the comparison operator `LT` (semantics in [the bytecode module](src/dafny/bytecode.dfy)) what is left to execute next is: either one instruction `STOP` or the section of the code that reverts (from `0x07`). 
The instrumentation of the execution of the bytecode with a Dafny `if-then-else` statement enables to track this two different paths. 



```dafny
/**
 *  This is a pattern that is frequently used to detect overflows for ADD.
 *
 *  @param  st  A state.
 *  @param  x   A u256.
 *  @param  y   A u256.
 *  @returns    A normal state  if no overflow, a revert state otherwise.
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

_What_ is verified is the following _correctness property_: for all inputs that satisfy the preconditions, 
- the body always terminates (as there is no loop this check is easy),  
- the `assert` statements are never violated, and 
- when the body of the method `OverflowCheck` terminates, the `ensures` statement hold.

As for the _How_, there several things that happen during this verification phase under the hood. In a nutshell, Dafny builds big _verification conditions_ (logical predicates), and it turns out that they are valid **if and only if** the correctness property above is true. 
Whether the verification conditions are valid is outsourced to a backend _SMT-solver_ (Z3).

### Results of the Verification

If we check the method `OverflowCheck`, the Dafny verifier indeed confirms that it is _correct_.
So what have we proved with this process?
Several interesting properties:  

- first, we have proved correctness **for all inputs** (satisfying the preconditions). It is a symbolic and logical reasoning process, not a _testing_ process. This is equivalent to exhaustively testing all inputs (and there are more than `2^257` possible inputs).
- second, with `Post0` we have a guarantee that the code snippet never runs out of gas. Of course this is true provided there is enough gas initially, as per `Pre1` which gives us a lower bound on what is needed to avoid an out-of-gas exception.
- third, we have proved that no exceptions related to stack under/overflow occur: otherwise we would 
reach an `INVALID` state which is ruled out by `Post0` 
- finally, we have proved that the code snippet correctly detects overflows in addition (`Post1` and `Post2`), and this for any values of `x` and `y` initially on the stack.

## A loop program 

The previous bytecode `OVERFLOW_CHECK` does not exercise a loop which makes relatively easy to verify.
The code below iterates a loop `c` times where `c` is an arbitrary `u8`, unsigned integer over 8 bits. 

We want to guarantee that this bytecode always terminates for any value of `c` and,
a suitable initial value of gas in the EVM.
What we are doing here is building a proof for a _family_ of bytecodes as `c` is a paramater of the bytecode itself. 
### What this bytecode is doing

The layout of the bytecode is as follows:

```assembly
-------------------
Address|Instruction
-------------------
0x00:   PUSH1 c
0x02:   JUMPDEST   <-------
0x03:   DUP1               |
0x04:   PUSH1 0x08         |
0x06:   JUMPI       ----   |
0x07:   STOP            |  |
0x08:   JUMPDEST    <---   |
0x09:   PUSH1, 0x01        |
0x0b:   SWAP1              |
0x0c:   SUB                |
0x0d:   PUSH1, 0x02        |
0x0f:   JUMP       --------
```

The bytecode initially pushes `c` at the top of the stack.
Let's assume the stack is initially empty. Then after executing `0x00` it is `[c]`.
The bytecode then iterates the following sequence of instructions:
1. duplicates top of the stack (`0x03`) and pushes a `JUMP` target `0x08`; the stack is `[0x08, c, c]`.
2. if `stack[1] > 0` then jump to `stack[0]` and otherwise go to next instruction `0x07`; pop two elements off the stack. This all happens with `JUMPI` at `0x06`. After this instruction the stack is `[c]`.
3. if we have not jumped in the previous step, the next instruction is `0x07` and we halt.
4. otherwise we are at `0x08`. From `0x08` to `0x0d`, decrement the top of the stack by one resulting in a stack `[c - 1]` and push a `JUMP` target `0x02`.
5. `JUMP` to `0x02` and pop top of the stack, i.e. go to step 1.

### Formal verification of the loop program

We assume that the starting state `st` of the EVM is such that:
1. the state is a non-failure state, with `PC=0` and there is room for pushing 3 elements on the stack (in the EVM the stack has limited capcity of 1024). This is captured by precondition `Pre0`;
2. we initially load the EVM with some gas, precondition `Pre1`. The amount of gas needed to terminate the computation depends on the value of `c`. It may take a while to figure out the formula but Dafny will _verify_ that it is indeed enough to run the program until completion.
3. the code to execute in the EVM is the bytecode above: this is enforced precondition `Pre2`.

```dafny
/**
 *  A program with a loop.
 *
 *  @param  c   The number of times to iterate the loop.
 *
 *  @note       The code iterates a loop `c` times by decremeting 
 *              a copy of `c` until it is zero. 
 *              We prove termination on this program and also 
 *              that it ends in a RETURN state. 
 *
 *              The stack content is unconstrained but there must be 
 *              enough capacity (3) to perform this computation. 
 */
method Loopy(st: State, c: u8) returns (st': State)
    requires /* Pre0 */ st.OK? && st.PC() == 0 && st.Capacity() >= 3
    requires /* Pre1 */ st.Gas() >= 
        3 * Gas.G_VERYLOW + Gas.G_JUMPDEST +
        c as nat * (2 * Gas.G_HIGH + 2 * Gas.G_JUMPDEST + 6 * Gas.G_VERYLOW)
        + Gas.G_HIGH

    requires /* Pre2 */ st.evm.code == Code.Create(
        [
        //  0x00   0x01   
            PUSH1, c, 
        //  0x02,     0x03   0x04 0x05
            JUMPDEST, DUP1, PUSH1, 0x08,
        //  0x06
            JUMPI, 
        //  0x07
            STOP,
        //  0x08      0x09   0x0a
            JUMPDEST, PUSH1, 0x01,
        //  0x0b   0x0c
            SWAP1, SUB, 
        //  0x0d   0x0e  0x0f
            PUSH1, 0x02, JUMP 
        ]
    );

    ensures /* Post0 */ st'.RETURNS?
{
    //  Execute PUSH1, c, JUMPDEST, DUP1, PUSH1, 0x08
    st' := ExecuteN(st, 4);
    //  verification variable to track decreasing counter
    ghost var count : u256 := c as u256;
    //  number of times we get into the loop.
    ghost var n: nat := 0; 

    while st'.Peek(2) > 0 
        invariant st'.OK?
        invariant st'.Gas() >= count as nat * (2 * Gas.G_HIGH + 2 * Gas.G_JUMPDEST + 6 * Gas.G_VERYLOW) + Gas.G_HIGH
        invariant st'.PC() == 0x06 
        invariant Stack.Size(st'.GetStack()) > 2
        invariant count == st'.Peek(2) == st'.Peek(1)
        invariant st'.Peek(0) == 0x08;
        invariant st'.evm.code == st.evm.code
        invariant n == c as nat - count as nat
        decreases st'.Peek(2)
    {
        assert st'.PC() == 0x06;
        //  Execute body of the loop
        st':= ExecuteN(st' ,10);
        count := count - 1;
        n := n + 1;
    }
    assert st'.PC() == 0x06;
    //  Check we iterated the loop c times.
    assert n == c as nat;
    //  JUMPI, STOP
    st' := ExecuteN(st', 2);
}
```

To verify that the loop iterates `c` times we use a _verification_ `ghost` variable `n` to record
the number of times we hit the instruction at `0x08`.
We also use a `ghost` variable `count` to keep track of the value of the loop counter which is actually on the stack.
Te fact that we iterate the loop `c` times is specified as `assert c == n` at the end the method `Loopy`.
And normal termination of the bytecode is specified by postcondition `Post0`.

So **How does it work?**

To verify this bytecode we instrument it.
The execution of the bytecode is _monitored_ by some Dafny code. 
This includes tracking whether we are iterating the loop body or not.
We can think about the instrumented code in `Loopy` as if we had two programs: the bytecode on the EVM executed with `ExecuteN` function, and in parallel a monitor that keeps track of where we are and can observe the state of the EVM but _not influence it_.

For instance, our monitor can check the value of the third element of the stack, `st'.Peek(2)` and 
according to its value, predicts the next instruction to be executed.
If  `st'.Peek(2)` it predicts that `PC=0x06` and the result of the `JUMPI` will be the loop body.
We then execute 9 more steps.
Otherwise it predicts that the next two steps will end the program (exit the `while` loop).

What if our predictions are wrong? The method will not verify as we won't be able to execute 10 instructions without
encountering an `INVALID` state.

And **what do we gain from this instrumentation?**

We can define _loop invariants_ which are predicates that must hold on the loop entry, and must be maintained by the loop body. 
By doing so we instrument the bytecode with some checks at regular intervals.
We can ensure that the loop terminates by providing a _ranking function_ (`decreases`). 
### Results 
Dafny successfully verifies our method `Loopy` which means that the invariants are actually loop invariants, and the postcondition and `assert` statements always hold.
As can be readily seen, the instrumentation and specification of the correctness criteria (pre- and postconditions, invariants) is much larger than the code to execute the bytecode, but this is expected in a formal verification world.

What we have proved in this bytecode is:
- the execution always terminates,for all values of `c`, and for any initial state of the EVM that satisfies the preconditions.
- the loop is iterated `c` times.
- there is no stack under/overflow.
- if we start with enough gas (`Pre1`) there is no out of gas exception.
 

