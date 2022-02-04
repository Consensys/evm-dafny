
<!-- [![Build Status](https://circleci.com/gh/ConsenSys/eth2.0-dafny.svg?style=shield)](https://circleci.com/gh/ConsenSys/workflows/eth2.0-dafny)  -->
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0) 
[![made-for-VSCode](https://img.shields.io/badge/Made%20for-VSCode-1f425f.svg)](https://code.visualstudio.com/)
[![lemmas](https://img.shields.io/badge/Lemmas-0-yellow.svg)](https://shields.io/) 
[![Checks](https://img.shields.io/badge/DafnyVerify-Verified-darkgreen.svg)](https://shields.io/) 

 <!-- ![GitHub commit activity](https://img.shields.io/github/commit-activity/w/PegaSysEng/eth2.0-dafny?style=flat) -->

# Overview / Objectives

This project aims at formally verifying the absence of runtime errors (array-out-of-bounds, over/underflows, ...) in some Arbitrum contracts. 

To achieve this, we use the capabilities of the verification-aware programming language [Dafny](https://github.com/dafny-lang/dafny).

# Resources

Arbitrum Documentation:

* [Arbitrum](https://github.com/OffchainLabs/arbitrum)
* [Arb-os](https://github.com/OffchainLabs/arb-os)
* [internals](https://developer.offchainlabs.com/docs/inside_arbitrum)

Some interesting papers and/or talks:

* [Usenix 2018 paper on Arbitrum (PDF)](https://www.usenix.org/system/files/conference/usenixsecurity18/sec18-kalodner.pdf)
* [Usenix 2018 presentation](https://www.usenix.org/conference/usenixsecurity18/presentation/kalodner)

# Methodology

Dafny provides extensive support for automated reasoning leveraging the power of state-of-start automated reasoning engines (SMT-solvers).
As a result, Dafny can assist in proving program **correctness** with respect to a specification.
In this project, the specifications are given as pre and post conditions. The abscence of runtime errors is checked by default in Dafny so there is not need to add specific specifications for them.
All the proofs can be **mechanically verified** using theorem provers.

# Results

We have analysed the contracts in the `arb-bridge-eth` package.

## Trusted Computing Base

We assume that the Dafny verifier is *sound*, i.e. if the verifier declares a program correct wrt a specification, then the program is actually correct wrt the specification.
This requirement is less demanding than that the Dafny compiler/verifier be bug-free (it is not, and there is a list of issues to be resolved.)
For instance, if the Dafny parser/compiler/verifier crashes because of a bug, it does not erroneously declare our program correct.

## Scope of the verification

Here is a list of what is not covered by this verification project:

- external components e.g. `sha256`, `keccak256` are not part of the verification effort.
The functions that were not analysed are marked with the `{:extern}` Dafny attribute.
For these functions we may provide a specification (pre and post conditions) and because they are externally defined  the specification is **assumed to hold** when proving other components. 

- the visibility attributes `public, private, etc` are ignored (although we have added them as Dafny attributes they are ignored by the Dafny verifier). This is not a limitation as the Solidity compiler already checks that these attributes are compatible across contracts.

- the attribute `payable` is also ignored.
This is not a theoretical limitation as we can check that (the semantics of) this attribute is properly implemented in each function; examples are available in [this repo](https://github.com/ConsenSys/solidity-to-dafny-examples).

- the memory attributes `storage`, `memory` are ignored.
In some examples we also have used Dafny `sequences` rather than `arrays`. This has no impact on the verification of runtime errors as Dafny arrays and sequences are *equivalent* 
when dereferencing and generates the same runtime errors. 

# How to check the proofs?

We have checked the proofs with Dafny 3.3.0.
To mechanically check the proofs (including absence of runtime errors), it suffices to run the Dafny verifier on the contracts.
We explain in this section how to do so.

## Using a Docker container with Dafny

Pre-requisites:

1. a working installation of [Docker](https://docs.docker.com),
2. a fork or clone of this repository.

A simple way to check the proofs is to use a pre-configured installation of Dafny on a Docker container.

On Unix-based system, `cd` to the root directory of your working copy of this repository.
```
/home/user1/ $ git clone git@github.com:PegaSysEng/eth2.0-dafny.git
/home/user1/ $ cd arbitrum-dafny
/home/user1/arbitrum-dafny $ 
```

The bash scripts ``verifyAll.sh`` can be used to verify the files in a given directory.

The next commands will start a [Docker container](https://hub.docker.com/repository/docker/franck44/linux-dafny) with Dafny pre-installed, and mount your local working directory as a volume in the Docker machine (this way you can access it from the running Docker machine):
```
/home/user1/arbitrum-dafny $ docker run -v /home/user1/arbitrum-dafny:/arbitrum-dafny -it franck44/linux-dafny /bin/bash
root@749938cb155d:/# cd arbitrum-dafny/
root@749938cb155d:/arbitrum-dafny# dafny /dafnyVerify:1 /compile:0 src/dafny/arbitrum/packages/arb-bridge-eth/contracts/rollup/RollupCore.dfy
Dafny 3.3.0.31104

Dafny program verifier finished with 23 verified, 0 errors
root@749938cb155d:/arbitrum-dafny# 
```
## Install Dafny on your computer

Pre-requisites:

* install Dafny, see [our Dafny wiki](wiki/dafny.md).
* clone or fork this repository.

Assuming you have a running Dafny compiler, you may use the following command line to check a `*.dfy` file:
```
> dafny /dafnyVerify:1 /compile:0  /timeLimit:60 src/dafny/arbitrum/packages/arb-bridge-eth/contracts/rollup/RollupCore.dfy
Dafny 3.3.0.31104

Dafny program verifier finished with 23 verified, 0 errors
```

