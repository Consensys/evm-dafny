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
include "../../dafny/gas.dfy"

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
   *  Starting from an OKState with 2 elements on the stack, check expansion
   *  sizes.
   */
  method MSTORE_01_Proofs(vm: OKState)
    requires Stack.Size(vm.GetStack()) >= 2
  {
    //  Compute new state
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

  //  Create an EVM using Berlin gas function
  import Gas

  /**
   *  Check gas consumption of MSTORE.
   *  Starting from an OKState with 2 elements on the stack.
   */
  method MSTORE_02_Proofs(vm: OKState)
    requires Stack.Size(vm.GetStack()) >= 2
    requires vm.MemSize() <= MAX_U256
    requires vm.Gas() >= Gas.G_VERYLOW;
  {
    //  address is in range, no expansion
    if vm.Peek(0) as nat + 31 < vm.MemSize() {
      var r := Bytecode.MStore(Gas.GasBerlin(MSTORE, vm));
      assert r.Gas() == vm.Gas() - Gas.G_VERYLOW;
    }

    // memory is empty, address required is 0, Expansion should be 32 bytes
    if vm.Peek(0) == 0 && vm.MemSize() == 0 && vm.Gas() >= 200 {
        assert vm.Peek(0) as nat + 31 >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(vm.Peek(0) as nat + 31);
        //  expansion is 32 bytes
        assert ex == 32;
        var exCost := Gas.ExpansionSize(vm.evm.memory, vm.Peek(0) as nat, 32);
        assert exCost == (Gas.G_MEMORY * 32 + 2) / 32; 

        var r := Bytecode.MStore(Gas.GasBerlin(MSTORE, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_VERYLOW + (Gas.G_MEMORY * 32 + 2) / 32);
    }

    //  memory is 32 bytes, address is 16. Expansion to 64 bytes.
    if vm.Peek(0) == 16 && vm.MemSize() == 32 && vm.Gas() >= 200 {
        assert vm.Peek(0) as nat + 31 >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(vm.Peek(0) as nat + 31);
        //  expansion is 64 bytes
        assert ex == 64;
        var exCost := Gas.ExpansionSize(vm.evm.memory, vm.Peek(0) as nat, 32);
        assert exCost == ((Gas.G_MEMORY * 64 + 8) / 32) - ((Gas.G_MEMORY * 32 + 2) / 32); 
        var r := Bytecode.MStore(Gas.GasBerlin(MSTORE, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_VERYLOW + exCost);
    }
  }
}
