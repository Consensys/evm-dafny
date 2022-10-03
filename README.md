<!-- [![Build Status](https://circleci.com/gh/ConsenSys/eth2.0-dafny.svg?style=shield)](https://circleci.com/gh/ConsenSys/workflows/eth2.0-dafny)  -->
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![made-for-VSCode](https://img.shields.io/badge/Made%20for-VSCode-1f425f.svg)](https://code.visualstudio.com/)
[![lemmas](https://img.shields.io/badge/Lemmas-0-yellow.svg)](https://shields.io/)
[![Checks](https://img.shields.io/badge/DafnyVerify-Verified-darkgreen.svg)](https://shields.io/)

 <!-- ![GitHub commit activity](https://img.shields.io/github/commit-activity/w/PegaSysEng/eth2.0-dafny?style=flat) -->

# Table of Contents

1. [Overview](#overview)
   1. [Dafny](#dafny)
   1. [Example](#example)
1. [Building](#building-the-code)
1. [Contributing](#contributing)
1. [Resources](#resources)

# Overview

The aim of this project is to develop a functional specification of
the [Ethereum Virtual
Machine](https://ethereum.org/en/developers/docs/evm/) in
[Dafny](https://github.com/dafny-lang/dafny).  Developing this
specification in Dafny allows us to apply [formal
reasoning](https://en.wikipedia.org/wiki/Formal_methods) to Smart
Contracts at the EVM Bytecode level.  For example, one can prove that
certain key properties are maintained by the contract.  We choose
Dafny over other verification systems
(e.g. [Coq](https://en.wikipedia.org/wiki/Coq) or
[Isabelle/HOL](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant)))
because it is relatively accessible to someone without significant
prior experience.

Our functional specification is also _executable_, meaning that we can
run contracts using it and compare their output with existing clients
(e.g. [Geth](https://geth.ethereum.org/)).  In particular, we are
interested in comparing against the [Ethereum Reference
Tests](https://github.com/ethereum/tests) and have made some progress
towards this.

## Dafny

[Dafny](https://github.com/dafny-lang/dafny) supports automated
software verification by leveraging the power of state-of-the-art
automated theorem provers (e.g with [SMT
solvers](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
like [Z3](https://en.wikipedia.org/wiki/Z3_Theorem_Prover)).  This
means Dafny can prove a program is **correct** with respect to its
specification.  To do this, Dafny requires the developer to provide
[preconditions](https://en.wikipedia.org/wiki/Precondition) and
[postconditions](https://en.wikipedia.org/wiki/Postcondition) where
appropriate, along with [loop
invariants](https://en.wikipedia.org/wiki/Loop_invariant) as
necessary.

_In this project, we are providing a specification of the Ethereum
Virtual Machine against which other programs (e.g. in EVM Bytecode)
can be verified._

## Example

As a simple example, consider the following specification given for
the [`ADD`](https://ethereum.org/en/developers/docs/evm/opcodes/)
bytecode:

```Dafny
/**
 * Unsigned integer addition with modulo arithmetic.
 */
function method Add(st: State) : State
requires !st.IsFailure() {
  var OK(vm) := st;
  //
  if st.Operands() >= 2
  then
    var lhs := st.Peek(0) as int;
    var rhs := st.Peek(1) as int;
    var res := (lhs + rhs) % TWO_256;
    st.Pop().Pop().Push(res as u256).Next()
  else
    State.INVALID
}
```

This tells us that `ADD` requires _two operands_ on the stack
(otherwise, the exceptional `INVALID` state is reached).  Furthermore,
addition employs _modulo arithmetic_ (hence, overflows wrap around)
and that the final result is pushed onto the stack after the operands
are popped.

# Building the Code

This repository uses [`gradle`](https://gradle.org/) as the de facto
build system.  To build the code, you need the following components:

* **[Java 11](https://openjdk.org/)** (or greater)

* **[Dafny 3.7](https://github.com/dafny-lang/dafny)** (or greater).

* **[Gradle 7](https://gradle.org)** (or greater)

With these installed, you can build the code using the following command:

```
> gradle build
```

This will verify the codebase using Dafny along with some examples,
generate a Java implementation of the `EVM`, and run two test suites
against it in Java.

# Generating Trace Tests

The tests used for the Dafny EVM are stored in the `tests/` directory.
These tests are generated from the [Ethereum reference
tests](https://github.com/ethereum/tests) using Geth's `evm` tool.
Each test is a `json` file similar in structure to that used by the
Ethereum reference tests, except that they include _full_ trace data
(i.e. the state of the EVM after every execution step).

To regenerate all the trace tests, you need to ensure `fixtures`
submodule is updated appropriately.  If you originally employed `git
clone --recursive` when cloning the repository, then you don't need to
do anything.  Otherwise, you can do this:

```
git submodule update --init
```

Using `gradle` one can now regenerate all the trace tests as follows:

```
> gradle testgen
```

This can take several minutes to complete, and requires that Geth's
`evm` tool is installed and visible on `PATH`.  Furthermore, the test
generate process is governed by the files `tests/includes.txt` and
`tests/excludes.txt`.  The former determines which of the reference
tests can be included, whilst the latter identifies specific cases to
exclude.  Finally, the trace generation process is managed by the
[EvmTools](https://github.com/DavePearce/EvmTools) framework.

# Contributing

See the [CONTRIBUTORS](CONTRIBUTORS.md) file for more information on
contributing to this repository.  By default contributors accept the
terms of the license.  We also endeavour to follow the conventions of
the Dafny [style
guide](https://github.com/dafny-lang/dafny/blob/master/docs/StyleGuide/Style-Guide.md).


# Resources
Some useful links:

* the Berlin version of the [yellow paper (YP)](https://ethereum.github.io/yellowpaper/paper.pdf)
* An complete [Introduction to the EVM](https://ethereum.org/en/developers/docs/evm/), Ethereum foundation
* A [Tutorial on the YP specification](https://ethereum.org/sr/developers/tutorials/yellow-paper-evm/),  (Ethereum foundation)
* the K-framework EVM semantics [KEVM, jellowpaper](https://jellopaper.org)
* the [Main EVM semantics](https://jellopaper.org/evm/) in Jellow paper (K framework)
* A [Quick reference to EVM opcodes](https://github.com/wolflo/evm-opcodes)
* An [Interactive reference to EVM opcodes](https://www.evm.codes)
* The Yul intermediate representation [Yul documentation](https://docs.soliditylang.org/en/v0.8.10/yul.html)
* Another proposal [Yul+](https://fuellabs.medium.com/introducing-yul-a-new-low-level-language-for-ethereum-aa64ce89512f)
