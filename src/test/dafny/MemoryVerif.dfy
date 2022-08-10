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
 
include "../../dafny/bytecode.dfy"

/**
 *  Provide some verification for properties of Memory opcodes. 
 */
abstract module MemoryVerif_01 {

  import opened Int
  import opened Opcode
  import Bytecode 
  import opened EvmState

  /**
   *  Check MSTORE.
   *  Starting from an OKState with 2 elements on the stack.
   */
  method MSTORE_01_Proofs(vm: OKState) 
    requires Stack.Size(vm.GetStack()) >= 2
  {
    var r := Bytecode.MStore(vm); 
    var address := vm.Peek(0) as nat;
    //  address + 31 bytes fit in memory.
    assert vm.Peek(0) as nat + 31 < MAX_U256 <==> !r.IsFailure();

    //  address + 31 bytes are already in memory.
    if vm.Peek(0) as nat + 31 < vm.MemSize() <= MAX_U256 {
      assert !r.IsFailure() && r.MemSize() == vm.MemSize();
      assert r.evm.memory.contents[..address] == vm.evm.memory.contents[..address];
      assert r.evm.memory.contents[address + 32..] == vm.evm.memory.contents[address + 32..];
    }

    //  address + 31 bytes are above memory size, but fit in memory.
    if vm.MemSize() <= vm.Peek(0) as nat + 31 < MAX_U256 {
      assert r.MemSize() > vm.MemSize();
      assert r.MemSize() - 32 <= vm.Peek(0) as nat + 31;
    }
  }
}

