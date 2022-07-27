<!-- [![Build Status](https://circleci.com/gh/ConsenSys/eth2.0-dafny.svg?style=shield)](https://circleci.com/gh/ConsenSys/workflows/eth2.0-dafny)  -->
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![made-for-VSCode](https://img.shields.io/badge/Made%20for-VSCode-1f425f.svg)](https://code.visualstudio.com/)
[![lemmas](https://img.shields.io/badge/Lemmas-0-yellow.svg)](https://shields.io/)
[![Checks](https://img.shields.io/badge/DafnyVerify-Verified-darkgreen.svg)](https://shields.io/)

 <!-- ![GitHub commit activity](https://img.shields.io/github/commit-activity/w/PegaSysEng/eth2.0-dafny?style=flat) -->

# Overview / Objectives

The aim of this project is to develop a functional specification of
the [Ethereum Virtual
Machine](https://ethereum.org/en/developers/docs/evm/) in
[Dafny](https://github.com/dafny-lang/dafny).

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

# Methodology

[Dafny](https://github.com/dafny-lang/dafny) provides extensive support for automated reasoning leveraging the power of state-of-start automated reasoning engines (SMT-solvers).
As a result, Dafny can assist in proving program **correctness** with respect to a specification.
In this project, the specifications of functions are given as _pre_ and _post_ conditions. The abscence of runtime errors (under/overflows, division by zero, array/sequence out-of-bounds) is checked by default in Dafny so there is no need to add specific specifications for them.
All the proofs can be **mechanically verified** using theorem provers.

# Contributing

By default contributors accept the terms of the license. 
We also endeavour to follow the conventions of the Dafny [style guide](https://github.com/dafny-lang/dafny/blob/master/docs/StyleGuide/Style-Guide.md).






## Install Dafny on your computer

Pre-requisites:

* install Dafny, see [our Dafny wiki](wiki/dafny.md).
* clone or fork this repository.

Assuming you have a running Dafny compiler, you may use the following command line to check a `*.dfy` file:
```bash
> dafny /dafnyVerify:1 /compile:0  /timeLimit:60 src/dafny/arbitrum/packages/arb-bridge-eth/contracts/rollup/RollupCore.dfy
Dafny 3.3.0.31104

Dafny program verifier finished with 23 verified, 0 errors
```
