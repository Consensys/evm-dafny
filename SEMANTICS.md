
In this section, we explain how to navigate the semantics, why it is verified and how to execute bytecode.


# Table of Contents

1. [Understanding the Semantics](#reading-and-understanding-the-semantics)
1. [Verifying the Semantics](#verifying-the-semantics)
1. [Executing the Semantics](#executing-the-semantics)

# Reading and Understanding the Semantics

The semantics of opcodes is written in a functional style in  [bytecode.dfy](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/bytecode.dfy).

For instance, the function `Add` below gives the semantics of opcode `ADD` (you can see how in the # [Executing EVM Bytecode](#executing-evm-bytecode) below):

```dafny
/**
 * Unsigned integer addition with modulo arithmetic.
 *
 * @param   st  A state.
 * @returns     The state after executing an `ADD` or an `Error` state. 
 */
function method Add(st: State): (st': State)
requires st.IsExecuting() 
ensures st'.OK? <==> st.Operands() >= 2
{
    if st.Operands() >= 2
    then
        var lhs := st.Peek(0) as int;
        var rhs := st.Peek(1) as int;
        var res := (lhs + rhs) % TWO_256;
        st.Pop().Pop().Push(res as u256).Next()
    else
        State.INVALID(STACK_UNDERFLOW)
}
```
With a few simple definitions, this specification is easy to read:
- `st.Operands()` is the size of the stack in `st`,
- `st.Peek(k)` is the value of the k+1-th element in the stack of `st`, `0` being the `top`,
- `x.Pop()` and `x.Push()`  respectively applies pop and push to `x`,
- `x.Next()` increments the program counter in `x`. 
- the precondition (`requires`) indicates that we can only apply this function to non-failure states,
- the body of the function defines the next state as a composition of functions applied in sequence `Pop(), Pop(), Push(), Next()`.
- the condition under which the opcode fails is fully captured by `st.Operands() >= 2`
- the postcondition (`ensures`) specifies a necessary and sufficient condition for the operation `Add` to succeed.

This specification above may be contrasted to existing specifications and implementations of `Add`:
- [KEVM semantics](https://github.com/runtimeverification/evm-semantics/blob/master/include/kframework/evm.md#expressions)
- [py-evm implementation](https://github.com/ethereum/py-evm/blob/1af151ab218b905f4fdf7a285cbe14ebf094a7c4/eth/vm/logic/arithmetic.py#L16)
- [Geth implementation](https://github.com/ethereum/go-ethereum/blob/ec2ec2d08e28571dc189903f743cc3931da254a9/core/vm/instructions.go#L29)
- [Besu implementation](https://github.com/hyperledger/besu/blob/951153d8eea33d44e50cc0cef46b773c9fdc8851/evm/src/main/java/org/hyperledger/besu/evm/operation/AddOperation.java#L25)

# Verifying the Semantics

The Dafny specification of `Add` above is  _self-contained_ and clearly identifies the cases where the `Add` function results in an `INVALID` state (the `ensures` is necessary and sufficient condition for `Add` to succeed).
On top of that, the preconditions we provide (`requires`) _must_ hold every time the function `Add` is called. This guarantees that in our semantics defined as function composition, we never apply `Add` on a _non-executing_ (`INVALID`, `RETURNS`, etc) state.

Apart from clarity and simplicity, the Dafny-EVM semantics provides a high degree of _security_.
To illustrate this point, it is useful to look at the code of `Pop` and `Push`:

```dafny

//  The following functions are part opf the State datatype
//  An instance `this` is implicit.
/**
 * Pop word from stack.
 */
function method Pop(): State
  requires this.IsExecuting()
  // Cannot pop from empty stack
  requires this.Operands() >= 1 {
    OK(this.evm.(stack:= this.GetStack().Pop()))
  }

/**
 * Push word onto stack.
 */
function method Push(v:u256): State
  requires this.IsExecuting()
  requires this.Capacity() > 0 {
    OK(this.evm.(stack:= this.GetStack().Push(v)))
  }
```

The definitions of `Pop` and `Push` requires as preconditions a non-failure state (satisfying `IsExecuting()`), and some constraints on the stack _size_ or _capacity_.
In the EVM the stack has a maximum size of 1024, and if the current size is `k` the capacity is `1024 - k`.

**What roles do preconditions play and how do they help?**

In the definition of `Add` above, we define the next state by `st.Pop().Pop().Push(...).Next()` where `st` is the current state.
Using a verification-friendly language like Dafny triggers several checks at compile time and among them:

**every time we call a function `f`, the preconditions of `f` must hold.**

This is not a runtime check that is going to be performed on each call of `f` but a _compile-time_ check that must _provably_  always hold. 
This is part of what Dafny does when it _verifies_ the `Add` function: it checks that:
1. `st` has more than one operand and the call to `st.Pop()` satisfies the preconditions of `Pop`;
2. it also checks that `st.Pop()` satisfies the preconditions of `Pop` as we apply `Pop` to the previous result. This is the reason why we have the `if st.Operands() >= 2` in the definition of `Add` and this is what enables Dafny to _prove_ that the preconditions of the second call to `Pop` are satisfied. If you download the code and have Dafny installed, you may replace `if st.Operands() >= 2` by `if st.Operands() >= 1` in `Add`. Dafny will highlight the error by pointing to the line 
`var rhs := st.Peek(1) as int` indicating that the precondition of `Peek(1)` does not hold (`Peek(1)` also requires a stack size larger than 1.)
3. another check is performed on `st.Pop().Pop()` to ensure that stack capacity satisfies the preconditions of `Push`. The proof of this fact follows from the semantics of `Pop` that removes elements from the stack; so the capcity of the stack after `st.Pop().Pop()` is at least one (which is worst-case of the stack capacity is `st` is zero). 

All the previous checks provide a very high degree of security of the code, ensuring that we **never** call by mistake `Add` on a stack with one element. 
The verification-friendliness of Dafny does not stop at preconditions, but also enforces the following checks by default:

-  **type checks**: if a variable `v` is declared with type say `u8`, any assignment to `v` requires a proof that `0 <= v <= 255`. The same holds for more complex types. For instance [the type of the stack](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/core/stack.dfy) is a `seq<u256>` of size `<= 1024`. This means that every time we compute a state there must be a compile-time proof that the stack size is `<= 1024`. Thankfully Dafny can automatically prove this most of the time with out help from the programmer.
- **bound checks**: we use unbounded _lists_, `seq<.>` in Dafny to represent several components (e.g. the stack). Any access `s[i]` to an element at a given index `i` in a `seq<.>` `s` must be provably valid, i.e. `0 <= i < size(s)`. This rules out any programming error `index-out-of-bound` in our code base.
- **termination checks**: every loop or recursive function must provably _terminate_. Dafny checks termination for every piece of code, and this may require the programmer to add `ranking functions`.


**By using a verification-friendly language, we can provide machine-checkable guarantees about our code.**




# Executing the Semantics

An EVM is in a given state `s: State`. The effect of an _opcode_ `op` on the current state
is described in two separate functions `OpSem` and `OpGas` in [evm.dfy](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/evm.dfy):

```dafny
/** The semantics of opcodes.
  *
  *  @param op   The opcode to look up.
  *  @param s    The state to apply the opcode to.
  *  @returns    The new state obtained after applying the semantics
  *              of the opcode.
  *  @note       If an opcode is not supported, or there is not enough gas
  *              the returned state is INVALID.
  */
function method OpSem(op: u8, s: State): State

/** The gas cost semantics of an opcode.
 *
 *  @param op   The opcode to look up.
 *  @param s    A state.
 *  @returns    The new state obtained having consumed the gas that corresponds to
 *              the cost of `opcode` is `s`.
 */
function method OpGas(op: u8, s: State): State
```

`OpGas` charges some gas to perform the computation associated to an opcode `op` in a given state `s`.
Most of the time the cost is fixed but sometimes the cost depends on the state, for instance if there is _memory expansion_. 

`OpSem` defines the _semantics_ of opcodes but does not take into account the gas consumption. 
For instance, the result of `OpSem(ADD, s)` is a new state `s'` which is equal to `s` except for the stack.   
`OpSem` uses the functions defined in [bytecode.dfy](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/bytecode.dfy) to compute the new state.
For instance a concrete definition of `OpSem` in  module [EvmBerlin](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/evms/berlin.dfy) defines the semantics of the `ADD` opcode as follows:
```dafny
function method OpSem(op: u8, s: State): State {
match s
  case OK(st) =>
    (
      match op
        ...
        case ADD =>  Bytecode.Add(s)
        ...
    )
}
```
where `Add` is the function that gives the semantics of opcode `ADD`.

Overall the new state of the EVM after executing an opcode `op` in state `s` is `s' = OpSem(opcode, OpGas(opcode, s))`.

The opcode to execute is part of the state `s` as `s` has the _code_ to execute and the _program counter_.
The `Execute` function below determines the next state: it extracts the opcode from the state `st`; if the opcode is valid, it computes the new state according to the semantics of the opcode, and otherwise we end up in an `INVALID` state. 

```dafny
/**
 *  Execute the next instruction.
 *  return
 *  @note       If the opcode semantics/gas is not implemented, the next
 *              state is INVALID.
 */
function method Execute(st: State): State
{
    match st.OpDecode()
        case Some(opcode) => OpSem(opcode, OpGas(opcode, st))
        case None => State.INVALID(INVALID_OPCODE)
}
```

Executing some bytecode can be achieved by creating a fresh EVM, and then applying the function `Execute` a number of times.

In practice we first have to define a _concrete_ module with concrete functions `OpSem` and `OpGas`.
The module [EvmBerlin](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/evms/berlin.dfy) is an example of such a concrete module.
Once we have a concrete module, we can execute some bytecode.
The example below is taken from [test.dfy](https://github.com/ConsenSys/evm-dafny/blob/master/src/test/dafny/test.dfy).

```dafny
method Test_EVM_01(x: u8)
{
// Bytecode to execute
var vm := EvmBerlin.InitEmpty(
    gas := 300,
    code := [
    PUSH1, x,
    PUSH1, 0x0,
    MSTORE,
    PUSH1, 0x1,
    PUSH1, 0x1F,
    RETURN
    ]);

// PUSH1 x
vm := EvmBerlin.Execute(vm);
// PUSH1 0x0
vm := EvmBerlin.Execute(vm);
// MSTORE
vm := EvmBerlin.Execute(vm);
// PUSH ... RETURN -- Execute 3 steps
vm := EvmBerlin.ExecuteN(vm,3);
//
assert vm.RETURNS?;
}
```

Several examples can be found in  [this test folder](https://github.com/ConsenSys/evm-dafny/tree/master/src/test/dafny).