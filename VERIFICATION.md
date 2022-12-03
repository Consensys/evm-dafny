

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
1. [Bytecode Optimisations](#evm-optimisations)
    1.  [Swapn Pop^n](#a-simple-pattern-problem-statement)
        1.  [Case SWAP1](#the-case-n--1)
            1. [How does it work?](#how-does-it-work)
            1. [Results](#results-1)
        1.  [General Case](#general-case)
            1. [How does it work?](#how-does-it-work-1)
            1. [Results](#results-2)

# Verifying Bytecode

## An Overflow Checker

### The code and the objective

The example below is a code snippet in [this example file](src/test/dafny/FM-paper.dfy).

First some bytecode is created using the `Code.Create` function from [the EVM module](src/dafny/evm.dfy).
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

Detecting overflows in _addition modulo_ a given number can be done by first computing the result of an addition modulo, and then checking a property of the result against one of the inputs.
In other words, there is a necessary and sufficient condition to detect overflows on addition modulo.
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
- C1: the addition of `x` and `y` _as if there were natural numbers_ (no modulo) is larger than `MAX_U256 = 2^256 - 1`,
- C2: the addition of `x` and `y` _modulo_ `2^256` is less than `x` (`y` would work too as the `+` is symmetric).

Dafny successfully verifies this lemma, using clever **automated reasoning** and an SMT-solver in the backend.
What we end up with is a _machine-checkable proof_ (the lemma is written as a program, and the program is verified by Dafny) that the lemma is valid _for all inputs `x` and `y` of type `u256`_.
We can now use this fact to write an overflow checker and this is exactly what  the `OVERFLOW_CHECK` code snippet does. 

### Formally Verifying the Overflow Checker
In order to verify that the overflow checker is _correct_ we need a few things:
1. a _formal specification_ of what the correctness property is,
2. a mechanism to _reason_ about the bytecode.

To do so we are going to write a Dafny program, a `method OverflowCheck` (below) that captures the specification and the correctness criteria:

- **the inputs** `x` and `y`:  there are input parameters of `OverflowCheck` together with a state `st:State` of an EVM. The inputs can take _arbitrary_ values but we add some reasonable contraints on them defined by preconditions (`requires`):
    - `Pre0` indicates that we start in a non-failure state, with the Program Counter `PC` pointing to instruction at address `0x00`.
    - `Pre1`: we assume the amount of `gas` in the EVM is larger than a certain amount. The values used here are defined for the Berlin version of the EVM semantics and available in [the Gas module](src/dafny/gas.dfy).
    - `Pre2`: the initial stack contains the two values `x` and `y` with `x` at the top with _`x` and `y` **arbitrary values** of type `u256`_.
    - `Pre3`: the code that is currently executed in the EVM is the `OVERFLOW_CHECK` code above.
- **the correctness criteria**: this is captured by _postconditions_ (`ensures`). The postconditions _formally_ and _logically_ define our correctness criteria:
    - the body **always** terminates; this is enforced by Dafny and when the body terminates, the following postconditions hold:
    - `Post0`: the final state is either a normal stop or a revert. This excludes `out-of-gas` exception (we intend to provide enough gas in `Pre1` to avoid `out-of-gas` exceptions).
    - `Post1`: the final state is a revert **if and only if** an overflow occurs. Note that overflow is defined mathematically with unbounded natural numbers (`nat`).
    - `Post2`: the final state is a normal state  **if and only if** no overflow occurs. That postcondition logically follows from `Post0` and `Post1`.
- **the instrumented code**: to _run_ the code we use the `ExecuteN(s, k)` function in [the EVM module](src/dafny/evm.dfy). This function executes (at most) `k` steps of the code in `s`. If an invalid state (e.g. stack under/overflow, out-of-gas) is encountered before the `k`-th step the execution prematurely stops and returns the invalid state. The body of the method `OverflowCheck` below somehow _monitors_ what the bytecode is doing. If executes the first 4 instructions, resulting
in state `st' == ExecuteN(st, 4)`. Depending on the result (second element of the stack `st'.Peek(1)`) of the comparison operator `LT` (semantics in [the bytecode module](src/dafny/bytecode.dfy)) what is left to execute next is: either one instruction `STOP` or the section of the code that reverts (from `0x07`). 
The instrumentation of the execution of the bytecode with a Dafny `if-then-else` statement enables to track these two different paths. 



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

- first, we have proved correctness **for all inputs** satisfying the preconditions. It is a symbolic and logical reasoning process, not a _testing_ process. This is equivalent to exhaustively testing all inputs (and there are more than `2^257` possible inputs).
- second, with `Post0` we have a guarantee that the code snippet never runs out of gas. Of course this is true provided there is enough gas initially, as per `Pre1` which gives us a lower bound on what is needed to avoid an out-of-gas exception.
- third, we have proved that no exceptions related to stack under/overflow occur: otherwise we would 
reach an `INVALID` state which is ruled out by `Post0` 
- finally, we have proved that the code snippet correctly detects overflows in addition modulo (`Post1` and `Post2`), and this for any values of `x` and `y` initially on the stack.

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
        invariant st'.Operands() > 2
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
Ghost variables cannot be used to influence the control flow.
The fact that we iterate the loop `c` times is specified as `assert c == n` at the end the method `Loopy`.
And normal termination of the bytecode is specified by postcondition `Post0`.

So **How does it work?**

To verify this bytecode we instrument it.
The execution of the bytecode is _monitored_ by some Dafny code. 
This includes tracking whether we are iterating the loop body or not.
We can think about the instrumented code in `Loopy` as if we had two programs: the bytecode on the EVM executed with `ExecuteN` function, and in parallel a monitor that keeps track of where we are and can observe the state of the EVM but _not influence it_.

For instance, our monitor can check the value of the third element of the stack, `st'.Peek(2)` and 
according to its value, predicts the next instruction to be executed.
If  `st'.Peek(2) > 0` it predicts that `PC=0x06` and the result of the `JUMPI` will be the loop body.
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
 

# EVM Optimisations

Every computation on the EVM incurs some cost measured in _gas_.
To save on gas, some _optimisations_ can be applied to the bytecode. 
A _correct_ optimisation of a sequence of instructions `xi` into `opt(xi)` should satisfy at least two properties:

1. if executing `xi` from state `s` results in state `s'` then executing `opt(xi)` from `s` should result in `s''` that may differ from `s'` only for the values of `gas` and `pc`
2. from _any_ state `s`, the gas cost of executing `opt(xi)` should be less than the gas cost of executing `xi`.

There are several ways of optimising EVM bytecode ranging from constant propagation, detecting/replacing some patterns, etc. 
Some optimisations may look trivial and _correct_ but there are some known bugs related to optimisations that can result in observing outdated memory states [Overly Optimistic Optimizer — Certora Bug Disclosure](https://medium.com/certora/overly-optimistic-optimizer-certora-bug-disclosure-2101e3f7994d).


## A Simple Pattern: Problem Statement

Using our framework, we can formalise the correctness criterion above and also prove that some optimisations are correct.
We demonstrate this on a simple example from
[this Thesis](https://fenix.tecnico.ulisboa.pt/cursos/mma/dissertacao/1691203502343808).


Proposition 12 in [this Thesis](https://fenix.tecnico.ulisboa.pt/cursos/mma/dissertacao/1691203502343808) proposes to replace any sequence of the form `SWAPN POP^(n+1)` by `POP^(n+1)` (we use regular-language notation so `a^k` stands for `a` repeated `k` times).

That seems plausible as:
1. `SWAPN` for `1 <= N <= 16` swaps the element at index `0` (top of the stack) with the element at index `N`,
2. because we `POP` `N+1` times right after the `SWAPN`, the SWAP somehow does not matter: the first `N+1` elements are popped and the elements at index `N+2` and above are left unchanged.

We want to _formally_ prove that replacing `SWAPN POP^(n+1)` by `POP^(n+1)` is _correct_, and this for any (valid) input state. 
Moreover, we provide a machine-checkable proofs of this fact.

### The case N = 1

To build a machine-checkable proof of Proposition 12 we write a [Dafny program](https://github.com/ConsenSys/evm-dafny/blob/master/src/test/dafny/Optimisations.dfy), `Proposition12a` below, with the following features:

1. we start from an arbitrary state of an EVM, `vm`, with the constraints that the stack has more than 2 elements (and less than the maximum 1024). We also require that there is enough gas in the machine. This is specified by the `requires` clauses in the Dafny code below. If these constraints are not satisfied we may reach and `INVALID` state and won't be able to prove any useful property. 
1. we execute `POP POP` in _one_ EVM, `vm1`, starting from the initial state `vm`;
1. then we execute `SWAP1 POP POP` in _another_ EVM, `vm2`, starting from the same initial state `vm`;
1. we then assert that the states after executing `SWAP1 POP POP` and `POP POP` are the same upto the values of `gas` and `pc`.


```dafny 
/**
 *  Proposition 12: n + 1 consecutive Pop  <_gas SwapN n + 1 consecutive Pop
 *  Gas cost for POP is G_BASE and for SWAP G_VERYLOW
 *  
 *  @param  s   An initial stack content.
 *  @param  g   An initial value of gas.
 * 
 *  @note   Case n = 1
 */
method Proposition12a(s: seq<u256>, g: nat)
    /** Stack must have at least 2 elements. */
    requires 2 <= |s| <= 1024   
    /** Minimum gas needed. */
    requires g >= 2 * Gas.G_BASE + Gas.G_VERYLOW
{
    //  Get an EVM with some gas and an arbitrary stack `s`
    var vm := EvmBerlin.Init(gas := g, stk := s, code := []);

    //  execute 2 POPs
    var vm1 := vm;
    vm1 := ExecuteOP(vm1, POP);
    vm1 := ExecuteOP(vm1, POP);

    //  execute SWAP1 followed by 2 POPs
    var vm2 := vm;
    vm2 := ExecuteOP(vm2, SWAP1);
    vm2 := ExecuteOP(vm2, POP);
    vm2 := ExecuteOP(vm2, POP);

    //  States are the same except for gas and PC
    assert vm1.evm.(pc := 0, gas := 0) == vm2.evm.(pc := 0, gas :=0);
    //  Gas saved is Gas.G_VERYLOW
    assert vm2.Gas() == vm1.Gas() - Gas.G_VERYLOW;
    assert vm2.Gas() < vm1.Gas();
}    
```

#### How does it work?

First, we use an input parameter `s` to define the content of the EVM at the beginning.
Because it is an input parameter it can take any _arbitrary_ value, but must satisfy the size requirements `2 <= |s| <= 1024 `.
The same holds for the gas value in the initial state: we require that this is more than a certain amount that corresponds to one SWAP and 2 POPS (we could actually require two different values for the two EVMs).

Second, the `assert` statements in Dafny are _verification_ statements and must provably hold for any inputs.
If you use this code in VSCode, you may change `requires 2 <= |s| <= 1024`
into `requires 1 <= |s| <= 1024` and see the effects: Dafny cannot prove that a valid state is reached after the computations. 


#### Results

Dafny can successfully verify (without any extra proof hints) the previous `method` and what we have proved is the following: 

**for _any_ state of the EVM with more than 2 elements on the stack, and enough gas,**

1.  the two sequences `SWAP1 POP POP` and `POP POP` lead to the same states (except for the value of `gas` and `pc`),
1. the sequence `POP POP` is strictly less expensive than `SWAP1 POP POP`,
1.  the `method` `Proposition12a` is a machine-checkable proof.

### General Case.

The general case is more tricky as we have to prove it for any `1 <= N <= 16`. We could write separate methods
to prove each case, but we show here how to use `loop invariants` to reason about EVM bytecode.

#### Proof for `1 <= n <= 16`

The Dafny `method` below specifies the proof of the general case.

As for the case `N = 1`, we run the code and the optimised code in two different EVMs starting from the same state.
What is more complicated here is that we have to execute the `POP` n times where `n` is an input parameter of the proof.

The result is that the constraint on the initial state of the EVM must satisfy some requirements that take into account the value of `n`. You can check that `n = 1` yields the constraints we had for the `Case N = 1` above.

```dafny 
/**
 *  
 *  Proposition 12: n + 1 consecutive Pop  <_gas SwapN n + 1 consecutive Pop
 *  Gas cost for POP is G_BASE and for SWAP G_VERYLOW
 *  
 *  @param  n   As described above.
 *  @param  s   An initial stack content.
 *  @param  g   An initial value of gas.
 *
 *  @note       General case.
 *
 */
method Proposition12b(n: nat, s: seq<u256>, g: nat)
    requires 1 <= n <= 16 
    /** Stack must have at least n + 1 elements. */
    requires n + 1 <= |s| <= 1024
    /** Minimum gas needed. */
    requires g >= (n + 1) * Gas.G_BASE + Gas.G_VERYLOW
{
    var vm := EvmBerlin.Init(gas := g, stk := s, code := []);

    //  Execute n + 1 POPs in vm1.
    var vm1 := vm;
    for i := 0 to n + 1
        invariant vm1.OK?
        invariant vm1.Gas() == g - i * Gas.G_BASE
        invariant vm1.Operands() >= n - i
        invariant vm1.GetStack() == vm.SlicePeek(i, |s|)
    {
        vm1 := ExecuteOP(vm1, POP);
        assert vm1.OK?;
    }
    assert vm1.Gas() >= Gas.G_VERYLOW;
    //  Stack after n + 1 POPs is suffix of initial stack starting at index n + 1
    assert vm1.GetStack() == vm.SlicePeek(n + 1, |s|);

    //  Execute SWAPn and then n + 1 POPs in vm2. 
    var vm2 := vm;
    vm2 := Swap(vm2, n).UseGas(Gas.G_VERYLOW);

    for i := 0 to n + 1
        invariant vm2.OK? 
        invariant vm2.Gas() == g - i * Gas.G_BASE - Gas.G_VERYLOW
        invariant vm2.Operands() >= n + 1 - i
        invariant vm2.Operands() == vm.Operands() - i == |s| - i
        invariant vm2.SlicePeek(n + 1 - i, |s| - i) == vm.SlicePeek(n + 1, |s|)
    {
        vm2 := ExecuteOP(vm2, POP);
        assert vm2.OK?;
    }
    assert vm2.SlicePeek(0, |s| - n - 1) == vm.SlicePeek(n + 1, |s|);
    assert vm1.GetStack() == vm2.GetStack();
    assert vm2.Gas() == vm1.Gas() -  Gas.G_VERYLOW;
    assert vm2.Gas() < vm1.Gas();
}    
```

#### How does it work?

The code snippet for the first loop shows that it is a bit harder to prove that the two sequences `SWAPN POP^(n+1)` by `POP^(n+1)` are equivalent.
First we have to prove that we can perform `n + 1` POPs. 
This requires us to maintain a loop invariant,  `invariant vm1.Operands() >= n - i`, that ensures that there are enough elements of the stack at each iteration of the loop.
The same holds for gas: we have to prove that there is enough gas after each iteration, which is captured by the loop invariant `invariant vm2.Gas() == g - i * Gas.G_BASE - Gas.G_VERYLOW`.
The other invariants `invariant vm2.OK?` specifies that at each iteration we are in non-failure state. 
Second we have to show that the resulting states are the same. This requires us to prove another _loop invariant_
`invariant vm2.SlicePeek(n + 1 - i, |s| - i) == vm.SlicePeek(n + 1, |s|)` where:
1.  `x.SlicePeek(l, u)` is a stack made out of the elements of `x` from index `l` to `u - 1`,
1. the invariant specifies that, in `vm2`, the stack content after the next `n + 1 - i` elements is the same as the initial stack content in `vm`.

The code snippet for  `SWAPN POP^(n+1)` is split into `SWAPN` and then a loop that pops `n + 1` times.
The invariants for the `vm2` states are similar to the ones for `vm1`.

Overall, Dafny checks that the predicate tagged with attribute `invariant` are indeed maintained by the loops, and valid on entry.
Using the fact that the loop invariants are true after exiting the loop, and in conjunction with the exit condition `i == n + 1`, this enables us to obtain the two facts:

1. `assert vm1.GetStack() == vm.SlicePeek(n + 1, |s|);` from `invariant vm1.GetStack() == vm.SlicePeek(i, |s|)` and `i == n + 1`
1.  `assert vm2.SlicePeek(0, |s| - n - 1) == vm.SlicePeek(n + 1, |s|);` from `invariant vm2.SlicePeek(n + 1 - i, |s| - i) == vm.SlicePeek(n + 1, |s|)` and `i == n + 1`.

As ` vm2.SlicePeek(0, |s| - n - 1)` is the stack in `vm2`, 
if we combine them we can prove that `assert vm1.GetStack() == vm2.GetStack();` i.e. the two stacks are equal after executing the sequences  `SWAPN POP^(n+1)` and `POP^(n+1)`.

#### Results

Dafny successfully verifies this program (without any extra proof hints), and we obtain the following results:

**for _any_ state of the EVM with more than `n + 1` elements on the stack, and enough gas,**


1.  the two sequences `SWAPN POP^(N + 1)` and `POP^(N + 1)` lead to the same states (except for the value of `gas` and `pc`),
1. the sequence `POP^(N + 1)` is strictly less expensive than `SWAPN POP^(N + 1)`.
1.  the `method` `Proposition12b` is a machine-checkable proof.
