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

// include "./evm-opcodes.dfy"
// include "./evm-types.dfy"

abstract module K {

  const semantics: map<nat, nat -> nat> 
    
}

/**
 * Top-level definition of an Ethereum Virtual Machine.
 */
abstract module EVM {

  abstract module L {

    function method foo(): bool 
  }

  function f(): bool {
    L.foo()
  }

  import K  

  function f1(k: nat) : nat 
  {
    if k in K.semantics then 
      K.semantics[k](k)
    else 
      0 
  } 
  // import opened Int
  // import opened EVM_TYPES
  // import opened EVM_OPCODES 

  /** The semantics of the opcodes, as a state transformer. */
  // const semantics: map<u8, State -> State> 
  // := map[ 
  //   STOP := (s:State) => Stop(s)
  // ]   

  /** The gas cost of for executing an instruxction. */
  // const gas: map<u8, State -> nat> 
  //  = map[
  //       STOP := (_ => 2),
  //       PUSH1 := (s:State) => (if !s.IsFailure() then (if s.evm.pc == 2 then 3 else 4) else 0)
  // ]

  /**
   * Execute a single step of the EVM.  This either States in a valid EVM (i.e. so execution
   * can continue), or some form of halt (e.g. exceptional, revert, etc).
   */
  // function method execute(s:State): State 
  //     // requires s.OK? 
  // {
  //     var opcode := decode(s);
  //     if opcode in semantics then 
  //       semantics[opcode](s)
  //     else 
  //       // Invalid/unsupported opcode
  //       State.INVALID
  // }

  /**
   * Create a fresh EVM to execute a given sequence of bytecode instructions.
   * The EVM is initialised with an empty stack and empty local memory.
   */
  // function method create(context: Context.T, storage: map<u256,u256>, gas: nat, code: seq<u8>) : State
  // requires |code| <= MAX_U256 {
  //   var stck := Stack.create();
  //   var mem := Memory.create();
  //   var sto := Storage.create(storage);
  //   var cod := Code.create(code);
  //   var evm := EVM(stack:=stck,memory:=mem,storage:=sto,context:=context,code:=cod,gas:=gas,pc:=0);
  //   // Off we go!
  //   State.OK(evm)
  // }

  // =============================================================================
  // Microcode
  // =============================================================================

  /**
   * Decode next opcode from machine.
   */
  // function method decode(st:State) : u8
  //  // To execute a bytecode requires the machine is in a non-terminal state.
  // // requires st.OK? 
  // //  for this one we may keep the st.OK? requirement as returning INVALID 
  // //  is atets is not Ok does not make a lot of sense.
  // {
  //   match st 
  //     case OK(vm) => 
  //       // Destructure incoming state.
  //       // var OK(vm) := st;
  //       // Sanity check pc location
  //       if vm.pc < Code.size(vm.code)
  //       then
  //         Code.decode_u8(vm.code,vm.pc as nat)
  //       else
  //         EVM_OPCODES.INVALID 
  //     case _ =>  EVM_OPCODES.INVALID 
  // }

  
}
