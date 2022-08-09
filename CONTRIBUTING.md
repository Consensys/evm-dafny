

# Table of Contents

1. [Contributors](#contributors)
1. [Bugs/New Features](#Reporting-bug-or-requesting-afeature)
1. [FInalising implementation and Pushing to `master`](#pushing-to-master)
1. [Coding style](#coding-style)
1. [General guidelines](#general-guidelines)
1. [Commits messages](#commits-messages)
1. [Refactoring](#refactoring)
1. [Comments](#comments)


# Contributors
By default contributors accept the terms of the license.

At the moment the repo is private, so the following is relevant for the project contributors, presumably from CSI.

# Reporting bug or requesting a feature

To report a bug or request a new feature:

1. create a new issue with a meanigful title e.g. _Add support for CALL opcode_, or _Slice does not properly slice sequences of length one_
2. describe the issue/feature request: why is it needed, what is it going to add, what is the expected difficulty or impact on section of the existing code.

Ideally, bugs/new features may be described succintly.
For bugs, it is requested to describe how to reproduce/trigger the bug.  

# Working on fixing a bug or implementing a new feature
If you are ready to work on an issue, create a branch and start working on the issue.
For instance, for `issue10` with title `add support for opcode CALL`, you may create a branch `issue10` or `issue10-add-support-for-opcode-CALL`.
You can then commit and make incremental changes. 
When the bug is fixed or feature implemented, the code can be pushed to the `master` branch via a pull request.

# Finalising implemenation and Pushing to `master`
Before pushing changes to `master`, it is suggested to:
1. run `gradle build`
2. fix any errors that can be triggered (type checking, compile errors, code generation, failing tests)

Ideally, changes to `master` should be made via a pull request.

# Coding style
At the moment there is no code formatter for Dafny. 
We endeavour to follow the conventions of the Dafny [style
guide](https://github.com/dafny-lang/dafny/blob/master/docs/StyleGuide/Style-Guide.md).

# General guidelines
When fixing a bug or adding features, it is advisable to write specifications (pre- and post-conditions) for functions and/or tests them to identify defects early.
It also makes the project more robust as the proofs/tests will be checked/run in the future.

It is also helpful to add some documentation to the functions, e.g. à-la-JavaDoc:

```dafny
/**
  *  Execute the next instruction.
  *  
  *  @param  st  A state.
  *  @returns    The state reached after executing the instruction 
  *              pointed to by 'st.PC()'. 
  *  @note       If the opcode semantics/gas is not implemented, the next
  *              state is INVALID.
  */
  function method Execute(st:State) : State
  {
    match st.OpDecode()  
      case Some(opcode) => OpSem(opcode, OpGas(opcode, st))
      case None => State.INVALID
  }
```

# Commits message

We follow the [standard giudelines](https://gist.github.com/robertpainsi/b632364184e70900af4ab688decf6f53) for the message guidelines.
It is advisable to reference the issue related to the commit if any, `see #12`, or `fixes #12`.

# Refactoring
We sometimes have to refactor, which means improve the code base, or moving things around.
The process for pushing changes is the same as for fixing a bug or a feature.

# Comments in issue threads

Be mindful that comments in the issue tracker may become public if we make the repo public.
