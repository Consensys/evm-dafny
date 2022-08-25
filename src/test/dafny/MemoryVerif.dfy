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
  import Bytes

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

    //  address + 31 bytes fit in memory iff Store is successful.
    assert address + 31 < MAX_U256 <==> 
      !r.IsFailure() && ReadUint256(r.evm.memory.contents, address) ==  vm.Peek(1);

    //  address + 31 bytes are already in memory. New state should be OK.
    if address + 31 < vm.MemSize() <= MAX_U256 {
      assert !r.IsFailure();
      //  Size is unchanged
      assert r.MemSize() == vm.MemSize();
      //  only chunk impacted is  r.evm.memory.contents[address..address + 31]
      assert r.evm.memory.contents[..address] == vm.evm.memory.contents[..address];
      assert r.evm.memory.contents[address + 32..] == vm.evm.memory.contents[address + 32..];
      assert ReadUint256(r.evm.memory.contents, address) ==  vm.Peek(1); 
    }

    //  address + 31 bytes are above memory size, but fit in max memory size. 
    if vm.MemSize() <= address + 31 < MAX_U256 {
      assert r.MemSize() > vm.MemSize();
      //  Memory is expanded by 32 bytes
      assert r.MemSize() - 32 <= address + 31;

      assert |r.evm.memory.contents[address + 31..]| == |Bytes.Padding(r.MemSize() - address - 31 )|;
      assert r.evm.memory.contents[address + 32..] == Bytes.Padding(r.MemSize() - address - 32 );
      assert ReadUint256(r.evm.memory.contents, address) ==  vm.Peek(1); 

      if address < vm.MemSize() {
        //  the start address to store the word at is inside of memory
        assert r.evm.memory.contents[..address] == vm.evm.memory.contents[..address];
      } else {
        //  the start address to store the word at is outside of memory
        assert r.evm.memory.contents[..vm.MemSize()] == vm.evm.memory.contents;
      }
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
    var address := vm.Peek(0) as nat;

    //  address is in range, no expansion
    if address as nat + 31 < vm.MemSize() {
      var r := Bytecode.MStore(Gas.GasBerlin(MSTORE, vm));
      assert r.Gas() == vm.Gas() - Gas.G_VERYLOW;
    }

    // memory is empty, address required is 0, Expansion should be 32 bytes
    if address == 0 && vm.MemSize() == 0 && vm.Gas() >= 200 {
        assert address as nat + 31 >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(address as nat + 31);
        //  expansion is 32 bytes
        assert ex == 32;
        var exCost := Gas.ExpansionSize(vm.evm.memory, address as nat, 32);
        assert exCost == (Gas.G_MEMORY * 32 + 2) / 32; 

        var r := Bytecode.MStore(Gas.GasBerlin(MSTORE, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_VERYLOW + (Gas.G_MEMORY * 32 + 2) / 32);
    }

    //  memory is 32 bytes, address is 16. Expansion to 64 bytes.
    if address == 16 && vm.MemSize() == 32 && vm.Gas() >= 200 {
        assert address as nat + 31 >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(address as nat + 31);
        //  expansion is 64 bytes
        assert ex == 64;
        var exCost := Gas.ExpansionSize(vm.evm.memory, address as nat, 32);
        assert exCost == ((Gas.G_MEMORY * 64 + 8) / 32) - ((Gas.G_MEMORY * 32 + 2) / 32); 
        var r := Bytecode.MStore(Gas.GasBerlin(MSTORE, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_VERYLOW + exCost);
    }
  }

  /**
   *  Check MLOAD.
   *  Starting from an OKState with 2 elements on the stack, check expansion
   *  sizes.
   */
  method MLOAD_01_Proofs(vm: OKState)
    requires Stack.Size(vm.GetStack()) >= 2
  {
    //  Compute new state
    var r := Bytecode.MLoad(vm);
    var address := vm.Peek(0) as nat;

    //  address + 31 bytes fit in memory iff load is successful.
    assert address + 31 < MAX_U256 <==> 
      !r.IsFailure() && r.Peek(0) == ReadUint256(r.evm.memory.contents, address);

    //  address + 31 bytes are already in memory. New state should be OK.
    if address + 31 < vm.MemSize() <= MAX_U256 {
      assert !r.IsFailure();
      //  Size is unchanged
      assert r.MemSize() == vm.MemSize();
      //  Memory is unchanged
      assert r.evm.memory.contents == vm.evm.memory.contents;
    }

    //  address + 31 bytes are above memory size, but fit in max memory size. 
    if vm.MemSize() <= address + 31 < MAX_U256 {
      assert r.MemSize() > vm.MemSize();
      //  Memory is expanded by 32 bytes
      assert r.MemSize() - 32 <= address + 31;

      assert r.evm.memory.contents[..vm.MemSize()] == vm.evm.memory.contents;
      assert r.evm.memory.contents[vm.MemSize()..] == Bytes.Padding(r.MemSize() - vm.MemSize());
    }
  }

  /**
   *  Check MLOAD.
   *  Starting from an OKState with 2 elements on the stack.
   */
 
  /**
   *  Check gas consumption of MLOAD.
   *  Starting from an OKState with 2 elements on the stack.
   */
  method MLOAD_02_Proofs(vm: OKState)
    requires Stack.Size(vm.GetStack()) >= 2
    requires vm.MemSize() <= MAX_U256
    requires vm.Gas() >= Gas.G_VERYLOW;
  {
    var address := vm.Peek(0) as nat;

    //  address is in range, no expansion
    if address + 31 < vm.MemSize() {
      var r := Bytecode.MLoad(Gas.GasBerlin(MLOAD, vm));
      assert r.Gas() == vm.Gas() - Gas.G_VERYLOW;
    }

    // memory is empty, address required is 0, Expansion should be 32 bytes
    if address == 0 && vm.MemSize() == 0 && vm.Gas() >= 200 {
        assert address + 31 >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(address + 31);
        //  expansion is 32 bytes
        assert ex == 32;
        var exCost := Gas.ExpansionSize(vm.evm.memory, address, 32);
        assert exCost == (Gas.G_MEMORY * 32 + 2) / 32; 

        var r := Bytecode.MLoad(Gas.GasBerlin(MLOAD, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_VERYLOW + (Gas.G_MEMORY * 32 + 2) / 32);
    }

    //  memory is 32 bytes, address is 16. Expansion to 64 bytes.
    if address == 16 && vm.MemSize() == 32 && vm.Gas() >= 200 {
        assert address + 31 >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(address + 31);
        //  expansion is 64 bytes
        assert ex == 64;
        var exCost := Gas.ExpansionSize(vm.evm.memory, address, 32);
        assert exCost == ((Gas.G_MEMORY * 64 + 8) / 32) - ((Gas.G_MEMORY * 32 + 2) / 32); 
        var r := Bytecode.MLoad(Gas.GasBerlin(MSTORE, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_VERYLOW + exCost);
    }

    //  memory is 106 bytes, address is 90. Expansion to 128 bytes.
    var k := 106;
    if address == 90 && vm.MemSize() == 106 && vm.Gas() >= 5000 {
        assert address + 31 >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(address + 31);
        //  expansion is 64 bytes
        assert ex == 128;
        var exCost := Gas.ExpansionSize(vm.evm.memory, address, 32);
        assert exCost == ((Gas.G_MEMORY * 128 + (128 * 128) / 512) / 32) - 
          ((Gas.G_MEMORY * k + k * k / 512 ) / 32); 
        var r := Bytecode.MLoad(Gas.GasBerlin(MLOAD, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_VERYLOW + exCost);
    }
  }

  //  RETURN gas cost 
  method RETURN_02_Proofs(vm: OKState)
    requires Stack.Size(vm.GetStack()) >= 2
    requires vm.MemSize() <= MAX_U256
    requires vm.Gas() >= Gas.G_VERYLOW;
  {
    var address := vm.Peek(0) as nat;
    var len := vm.Peek(1) as nat;

    //  address is in range, no expansion
    if address + len < vm.MemSize() {
      var r := Bytecode.Return(Gas.GasBerlin(RETURN, vm));
      assert r.Gas() == vm.Gas() - Gas.G_ZERO;
    }

    // memory is empty, address required is 0 and length 2, Expansion should be 32 bytes
    if address == 0 && len == 2 && vm.MemSize() == 0 && vm.Gas() >= 200 {
        assert address + len >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(address + len);
        //  expansion is 32 bytes
        assert ex == 32;
        var exCost := Gas.ExpansionSize(vm.evm.memory, address, len);
        assert exCost == (Gas.G_MEMORY * 32 + 2) / 32; 

        var r := Bytecode.Return(Gas.GasBerlin(RETURN, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_ZERO + exCost);
    }

    //  memory is 32 bytes, address is 16, length is 17. Expansion to 64 bytes.
    if address == 16 && len == 17 && vm.MemSize() == 32 && vm.Gas() >= 200 {
        assert address + 31 >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(address + len);
        //  expansion is 64 bytes
        assert ex == 64;
        var exCost := Gas.ExpansionSize(vm.evm.memory, address, len);
        assert exCost == ((Gas.G_MEMORY * 64 + 8) / 32) - ((Gas.G_MEMORY * 32 + 2) / 32); 
        var r := Bytecode.Return(Gas.GasBerlin(RETURN, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_ZERO + exCost);
    }
  }

  //  REVERT gas cost 
  method REVERT_02_Proofs(vm: OKState)
    requires Stack.Size(vm.GetStack()) >= 2
    requires vm.MemSize() <= MAX_U256
    requires vm.Gas() >= Gas.G_VERYLOW;
  {
    var address := vm.Peek(0) as nat;
    var len := vm.Peek(1) as nat;

    //  address is in range, no expansion
    if address + len < vm.MemSize() {
      var r := Bytecode.Revert(Gas.GasBerlin(REVERT, vm));
      assert r.Gas() == vm.Gas() - Gas.G_ZERO;
    }

    // memory is empty, address required is 0 and length 2, Expansion should be 32 bytes
    if address == 0 && len == 2 && vm.MemSize() == 0 && vm.Gas() >= 200 {
        assert address + len >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(address + len);
        //  expansion is 32 bytes
        assert ex == 32;
        var exCost := Gas.ExpansionSize(vm.evm.memory, address, len);
        assert exCost == (Gas.G_MEMORY * 32 + 2) / 32; 

        var r := Bytecode.Revert(Gas.GasBerlin(REVERT, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_ZERO + exCost);
    }

    //  memory is 32 bytes, address is 16, length is 17. Expansion to 64 bytes.
    if address == 16 && len == 17 && vm.MemSize() == 32 && vm.Gas() >= 200 {
        assert address + 31 >= vm.MemSize();
        //  compute expanded size
        var ex := Memory.SmallestLarg32(address + len);
        //  expansion is 64 bytes
        assert ex == 64;
        var exCost := Gas.ExpansionSize(vm.evm.memory, address, len);
        assert exCost == ((Gas.G_MEMORY * 64 + 8) / 32) - ((Gas.G_MEMORY * 32 + 2) / 32); 
        var r := Bytecode.Revert(Gas.GasBerlin(REVERT, vm));
        assert r.Gas() == vm.Gas() - (Gas.G_ZERO + exCost);
    }
  }
}
