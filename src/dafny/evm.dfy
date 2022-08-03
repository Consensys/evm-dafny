/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
include "state.dfy"
include "util/ExtraTypes.dfy" 

/**
 * Top-level definition of an Ethereum Virtual Machine.
 */
abstract module EVM {
    import opened EvmState
    import opened Int
    import opened ExtraTypes

    /** The semantics of opcodes.
     *  It is defined as a total function from non failure states.
     */
    const SEMANTICS: map<u8, OKState -> State>

    /** Whether an opcode is supported. */
    // function method SupportedOpcode(op: u8): bool

    function method SEMANTICS2(op: u8): Option<OKState -> State> 

    function method GAS2(op: u8): Option<OKState -> nat> 

    const GAS: map<u8, OKState -> nat>

    function method Execute(st:State) : State
    // To execute a bytecode requires the machine is in a non-terminal state.
    requires !st.IsFailure()
    requires st.PC() < Code.Size(st.evm.code) as nat
    {
      var opcode := st.Decode();
      if opcode in SEMANTICS && opcode in GAS && st.Gas() >= GAS[opcode](st) as nat then
        //  Note: SEMANTICS and GAS not commutative.
        SEMANTICS[opcode](st.UseGas(GAS[opcode](st)))
      else
        // Invalid/unsupported opcode
        State.INVALID
  }

  function method Execute2(st:State) : State
    // To execute a bytecode requires the machine is in a non-terminal state.
    requires !st.IsFailure()
    requires st.PC() < Code.Size(st.evm.code) as nat
    {
      var opcode := st.Decode();
      if SEMANTICS2(opcode).Some? && GAS2(opcode).Some? && st.Gas() >= (GAS2(opcode).v)(st) as nat then
        //  Note: SEMANTICS and GAS not commutative.
        (SEMANTICS2(opcode).v)(st.UseGas((GAS2(opcode).v)(st)))
      else
        // Invalid/unsupported opcode
        State.INVALID
  }

  /**
    * Create a fresh EVM to execute a given sequence of bytecode instructions.
    * The EVM is initialised with an empty stack and empty local memory.
    */
  function method Create(context: Context.T, storage: map<u256,u256>, gas: nat, code: seq<u8>) : State
  requires |code| <= Code.MAX_CODE_SIZE {
      var stck := Stack.Create();
      var mem := Memory.Create();
      var sto := Storage.Create(storage);
      var cod := Code.Create(code);
      var evm := EVM(stack:=stck,memory:=mem,storage:=sto,context:=context,code:=cod,gas:=gas,pc:=0);
      // Off we go!
      State.OK(evm)
  }
}
