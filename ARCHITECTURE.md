# Table of Contents

1. [Overview](#overview)
1. [Architecture](#repoArch)
1. [Source Files](#sourceFilesi)
	1. [Top Layer Files](#top)
	1. [Middle Layer Files](#mid)
	1. [Low Layer Files](#low)


# Overview

The [evm-dafny](https://github.com/ConsenSys/evm-dafny) repository contains five directories and five stand-alone files the most remarkable of which are the following:

- [`github/workflows`](https://github.com/ConsenSys/evm-dafny/tree/master/.github/workflows) consists of the build process of different modules and their dependencies,
- [`fixture`](https://github.com/ethereum/tests/tree/9d91961e98e97ba319e089f31388d4685da9b362) contains the ethereum tests to generate, to test our system against,

- [`resources`](https://github.com/ConsenSys/evm-dafny/tree/master/resources) contains the log of tests which have been generated and our system is tested against,

- [`src`](https://github.com/ConsenSys/evm-dafny/tree/master/src) comprises the backbone of our system including the formal semantics of the Dafny-EVM. It contains three subdirectories:
	
	- [`dafny`](https://github.com/ConsenSys/evm-dafny/tree/master/src/dafny) consists of the Dafny-EVM Source Files as explained further below,
	- [`main`](https://github.com/ConsenSys/evm-dafny/tree/master/src/main/java) includes the Java interface to the Dafny,
	- [`test`](https://github.com/ConsenSys/evm-dafny/tree/master/src/test) contains simple tests implemented in dafny for checking the correctness of different opcodes  

- [`tests`](https://github.com/ConsenSys/evm-dafny/tree/master/tests) consists of the list of ethereum tests we are currently running,


- [`build.gradle`](https://github.com/ConsenSys/evm-dafny/blob/master/build.gradle) consists of build instructions with the `gradle` tool,
 
We organize the [Source Files](#sourceFiles) of the Dafny-EVM according to a three-layer architecture explained further below. 
# Architecture

The architecture of the [Source Files](#sourceFiles) comprises the three layers; top, middle and the bottom layer, as shown in the image below. The top of the stack image, shows the [Top layer] modules containing bytecode semantics and top-level types.  We locate in the middle of the image, modules of the [Middle Layer](#mid) which contain abstractions of the main components.  The bottom of the stack depicts the modules placed at the [Bottom Layer](#low) which specify fundamental primitives (e.g. for manipulating bytes and ints). 

<p align="center">
    <img width="450" src="https://github.com/ConsenSys/evm-dafny/tree/resources/stackArch.png" alt="Dafny-EVM Architecture">
</p>


# Source Files

The source files including our formalisation of the EVM semantics, the state, gas calculations, and helper modules appear under the directory [`src/dafny`](https://github.com/ConsenSys/evm-dafny/tree/master/src/dafny). The architecture of the source files accords with the three layer model explained above. 

## Top Layer

- [`evms`](https://github.com/ConsenSys/evm-dafny/tree/master/src/dafny/evms) contains modules each of which specify an extension of our EVM with a particular hardfork of users' choice, for example [`berlin.dfy`](https://github.com/ConsenSys/evm-dafny/tree/master/src/dafny/evms/berlin.dfy).

- [`opcodes.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/opcodes.dfy) encodes all of the EVM opcodes.

- [`evm.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/evm.dfy) provides a generic mechanism for building extensions on our EVM based on a hardfork of users' choice.

- [`state.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/state.dfy) specifies various EVM states and how to perform operations on them.

- [`bytecode.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/bytecode.dfy) includes the implementation of the EVM opcodes' semantics.

- [`gas.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/gas.dfy) specifies gas charging calculations.


## Middle Layer 
- [`code.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/code.dfy) is an implementation of read-only code region of the EVM.
- [`context.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/context.dfy) implements the execution context of a transaction.
- [`memory.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/memory.dfy) is a specification of the EVM's volatile memory.
- [`precompiled.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/precompiled.dfy) implements precompiled contracts.
- [`stack.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/stack.dfy) specifies the stack of EVM together with stack operations.
- [`storage.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/storage.dfy) is an implementation of the EVM storage including functionalities for performing operations on the storage.
- [`substate.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/substate.dfy) encodes the substate of the EVM.
- [`worldstate.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/worldstate.dfy) specifies the wold state of the ethereum.


## Bottom Layer

- [`ExtraTypes.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/ExtraTypes.dfy)
- [`bytes.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/bytes.dfy) implements an specification of machine bytes together with methods for performing operations on them.
- [`int.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/int.dfy) specifies machine words of various length both signed and unsigned.
- [`extern.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/extern.dfy) interfaces Dafny with Java.


 










