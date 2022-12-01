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
include "util/option.dfy"

/**
 * Top-level definition of an Ethereum Virtual Machine.
 */
abstract module EVM {
    import opened EvmState
    import opened Int
    import opened Optional

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

    /**
     * Create a fresh EVM to execute a given sequence of bytecode instructions.
     * The EVM is initialised with an empty stack and empty local memory.
     */
    function method Create(context: Context.T, world: map<u160,WorldState.Account>, gas: nat, code: seq<u8>, st: seq<u256> := []) : State
    // Code to executed cannot exceed maximum limit.
    requires |code| <= Code.MAX_CODE_SIZE
    requires |st| <= 1024
    // Account under which EVM is executing must exist!
    requires context.address in world {
        var stck := Stack.Make(st);
        var mem := Memory.Create();
        var wld := WorldState.Create(world);
        var cod := Code.Create(code);
        var sub := SubState.Create();
        var evm := EVM(stack:=stck,memory:=mem,world:=wld,context:=context,code:=cod,substate:=sub,gas:=gas,pc:=0);
        // Off we go!
        State.OK(evm)
    }

    /**
     *  Execute the next instruction
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

    function method ExecuteOP(st: State, op: u8): State
    {
          OpSem(op, OpGas(op, st))
    }

    /**
     *  Execute the next instruction
     *  return
     *  @note       If the opcode semantics/gas is not implemented, the next
     *              state is INVALID.
     */
    function method ExecuteN(st:State, steps: nat := 1): State
    decreases steps
    requires steps > 0
    {
        // Execute next instruction
        var nst := Execute(st);
        // Recurse as necessary
        if steps == 1 || !nst.OK? then nst else ExecuteN(nst,steps-1)
    }
}
