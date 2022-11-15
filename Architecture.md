# Table of Contents

1. [Repository Architecture](#repoArch)
1. [Dafny-EVM Source Files](#sourceFiles)
1. [Dafny-EVM Architecture](#architecture) 


# Repository Architecture

The [evm-dafny](https://github.com/ConsenSys/evm-dafny) repository contains five directories and five stand-alone files as follows:

- [`github/workflows`](https://github.com/ConsenSys/evm-dafny/tree/master/.github/workflows) consists of the build process of different modules and their dependencies,
- [`fixture`](https://github.com/ethereum/tests/tree/9d91961e98e97ba319e089f31388d4685da9b362) contains the ethereum tests to generate, to test our system against,

- [`resources`](https://github.com/ConsenSys/evm-dafny/tree/master/resources) contains the log of tests which have been generated and our system is tested against,

- [`src`](https://github.com/ConsenSys/evm-dafny/tree/master/src) comprises the backbone of our system including the formal semantics of the Dafny-EVM. It contains three subdirectories: [`dafny`](https://github.com/ConsenSys/evm-dafny/tree/master/src/dafny), [`main`](https://github.com/ConsenSys/evm-dafny/tree/master/src/main/java), and [`test`](https://github.com/ConsenSys/evm-dafny/tree/master/src/test),
	
	- `dafny` consists of the Dafny-EVM Source Files as explained further below,
	- `main` includes the Java interface to the Dafny,
	- `test` contains simple tests implemented in dafny for checking the correctness of different opcodes  

- [`tests`](https://github.com/ConsenSys/evm-dafny/tree/master/tests) consists of the list of ethereum tests we are currently running,

- [`LEGAL.md`](https://github.com/ConsenSys/evm-dafny/blob/master/LEGAL.md) explains the licensing of our software,

- [`README.md`](https://github.com/ConsenSys/evm-dafny/blob/master/README.md) provides an overview of the `evm-dafny` repository,

- [`build.gradle`](https://github.com/ConsenSys/evm-dafny/blob/master/build.gradle) consists of build instructions with the `gradle` tool,

- [`Contributors.md`](https://github.com/MiladKetabGhale/Playing/blob/master/CONTRIBUTORS.md) contains general guidelines about how to contribute to our repository, the coding style, and reporting bugs and issues among a few other things, 

- [`Architecture.md`]() is the current file.

# Dafny-EVM Source Files

The source files including our formalisation of the EVM semantics, the state, gas calculations, and helper modules appear under the directory [`src/dafny`](https://github.com/ConsenSys/evm-dafny/tree/master/src/dafny). It contains the following subdirectories and files:

- [`evms`](https://github.com/MiladKetabGhale/Playing/tree/master/src/dafny/evms) contains modules each of which specify an extension of our EVM with a particular hardfork of users' choice, for example [`berlin.dfy`](https://github.com/MiladKetabGhale/Playing/blob/master/src/dafny/evms/berlin.dfy).
 
- [`utils`](https://github.com/ConsenSys/evm-dafny/tree/master/src/dafny/util) consists of the following modules:
	- [`ExtraTypes.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/ExtraTypes.dfy)
	- [`bytes.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/bytes.dfy) implements an specification of machine bytes together with methods for performing operations on them.
	- [`code.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/code.dfy) is an implementation of read-only code region of the EVM.
	- [`context.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/context.dfy) implements the execution context of a transaction.
	- [`extern.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/extern.dfy) interfaces Dafny with Java.
	- [`int.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/int.dfy) specifies machine words of various length both signed and unsigned.
	- [`memory.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/memory.dfy) is a specification of the EVM's volatile memory.
	- [`precompiled.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/precompiled.dfy) implements precompiled contracts.
	- [`stack.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/stack.dfy) specifies the stack of EVM together with stack operations.
	- [`storage.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/storage.dfy) is an implementation of the EVM storage including functionalities for performing operations on the storage.
	- [`substate.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/substate.dfy) encodes the substate of the EVM.
	- [`worldstate.dfy`](https://github.com/ConsenSys/evm-dafny/blob/master/src/dafny/util/worldstate.dfy) specifies the wold state of the ethereum.

- [`opcodes.dfy`](https://github.com/MiladKetabGhale/Playing/blob/master/src/dafny/opcodes.dfy) encodes all of the EVM opcodes.

- [`evm.dfy`](https://github.com/MiladKetabGhale/Playing/blob/master/src/dafny/evm.dfy) provides a generic mechanism for building extensions on our EVM based on a hardfork of users' choice.

- [`state.dfy`](https://github.com/MiladKetabGhale/Playing/blob/master/src/dafny/state.dfy) specifies various EVM states and how to perform operations on them.

- [`bytecode.dfy`](https://github.com/MiladKetabGhale/Playing/blob/master/src/dafny/bytecode.dfy) includes the implementation of the EVM opcodes' semantics.

- [`gas.dfy`](https://github.com/MiladKetabGhale/Playing/blob/master/src/dafny/gas.dfy) specifies gas charging calculations.
 



# Dafny-EVM Architecture

<p align="center">
    <img width="600" src="https://github.com/ConsenSys/evm-dafny/tree/412-add-architecturemd-file/Arch_DafnyEvm.png" alt="Dafny-EVM Architecture">
</p>

The above image illustrates module dependencies in our system. Every file in the [Dafny-EVM Source Files](#sourceFiles) contains only one theory module named according to the file name in which it is located. In the architecture image above, an arrow from a module M1 to another module M2 depicts the dependency of M1 on M2. Note that module dependency is transitive. Moreover, modules appearing in the same color in the image are located in the same directory.  






