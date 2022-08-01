include "../../dafny/evm.dfy"
include "../../dafny/evms/berlin.dfy"

import opened Int
import opened Opcode

// Arbitrary limit for now
const GASLIMIT : nat := 100;

// Check most simple program possible
method test_Execute_01(x: u8)
requires x > 1
{
  // Initialise Bytecode
  var tx := Context.Create(0xabcd,[]);
  var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  // PUSH1 x
  vm := EvmBerlin.Execute(vm);  
  // PUSH1 0x2
  vm := EvmBerlin.Execute(vm);
  // MSTORE
  vm := EvmBerlin.Execute(vm);
  // PUSH
  vm := EvmBerlin.Execute(vm);
  // PUSH 
  vm := EvmBerlin.Execute(vm);
  // RETURN
  vm := EvmBerlin.Execute(vm);
  //
  assert vm.data == [x];
  // print vm.gas, "\n";
  assert vm.Gas() == GASLIMIT - 6;
}

// ===========================================================================
// Straightline Tests
// ===========================================================================

method {:test} test_basic_01() 
{
  var x := 3;
  // Initialise EVM
  var tx := Context.Create(0xabcd,[]);
  var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  // PUSH1 x
  vm := EvmBerlin.Execute(vm);
  // PUSH1 0x2
  vm := EvmBerlin.Execute(vm);
  // MSTORE
  vm := EvmBerlin.Execute(vm);
  // PUSH
  vm := EvmBerlin.Execute(vm);
  // PUSH
  vm := EvmBerlin.Execute(vm);
  // RETURN
  vm := EvmBerlin.Execute(vm);
  //
  expect vm.Gas() == GASLIMIT - 6;
  expect vm.data == [x], ("failed. vm.data=", vm.data); //, "failed";
}

// Write parameter into return data
method test_basic_02(x: u8)
requires x > 1
{
  var tx := Context.Create(0xabcd,[]);
  var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  //
  vm := Bytecode.Push1(vm,x);
  vm := Bytecode.Push1(vm,0);
  vm := Bytecode.MStore(vm);
  vm := Bytecode.Push1(vm,0x1);
  vm := Bytecode.Push1(vm,0x1F);
  vm := Bytecode.Return(vm);
  //
  assert vm.data  == [x];
}

// Add two values and return
method test_basic_03(x: u8, y: u8) returns (z:u16)
ensures z == (x as u16) + (y as u16)
{
  var tx := Context.Create(0xabcd,[]);
  var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[]);
  //
  vm := Bytecode.Push1(vm,x);
  vm := Bytecode.Push1(vm,y);
  vm := Bytecode.Add(vm);
  assert vm.Peek(0) == (x as u256) + (y as u256);
  vm := Bytecode.Push1(vm,0);
  vm := Bytecode.MStore(vm);
  vm := Bytecode.Push1(vm,0x2);
  vm := Bytecode.Push1(vm,0x1E);
  vm := Bytecode.Return(vm);
  // //
  return Bytes.ReadUint16(vm.data,0);
}

method test_basic_04(x: u8, y: u8) returns (z:u8)
requires x >= y
ensures z <= x
{
  var tx := Context.Create(0xabcd,[]);
  var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[PUSH1, y, PUSH1, x, SUB, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  //
  vm := Bytecode.Push1(vm,y);
  vm := Bytecode.Push1(vm,x);
  vm := Bytecode.Sub(vm); // x - y
  assert vm.Peek(0) == (x as u256) - (y as u256);
  vm := Bytecode.Push1(vm,0);
  vm := Bytecode.MStore(vm);
  vm := Bytecode.Push1(vm,0x1);
  vm := Bytecode.Push1(vm,0x1F);
  vm := Bytecode.Return(vm); 
  //
  return Bytes.ReadUint8(vm.data,0);
}

// ===========================================================================
// Branching Tests
// ===========================================================================

// This is an underflow test.  Either the contract reverts, or there was no underflow.
method test_branch_01(x: u8, y: u8) returns (z:u8, revert:bool)
  // Check revert only when overflow would have occurred.
  ensures revert <==> y > x
  // If didn't revert, then result is less.
  ensures !revert <==> (z <= x)
{
  var tx := Context.Create(0xabcd,[]);
  var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, y, GT, ISZERO, PUSH1, 0x0A, JUMPI, REVERT, JUMPDEST, PUSH1, x, PUSH1, y, SUB, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  //
  vm := Bytecode.Push1(vm,x);   // 0x00
  vm := Bytecode.Push1(vm,y);   // 0x02
  vm := Bytecode.Gt(vm);        // 0x04
  vm := Bytecode.IsZero(vm);    // 0x05
  vm := Bytecode.Push1(vm,0xA); // 0x06
  vm := Bytecode.JumpI(vm);     // 0x08
  //
  assert vm.evm.pc == 0x09 <==> y > x;
  if vm.evm.pc == 0x09 {
    vm := Bytecode.Revert(vm);  // 0x09
    return y,true;
  } else {
    // Happy path
    vm := Bytecode.JumpDest(vm); // 0xA
    assert x >= y;
    vm := Bytecode.Push1(vm,y);
    vm := Bytecode.Push1(vm,x);
    vm := Bytecode.Sub(vm); // x - y
    assert vm.Peek(0) == (x as u256) - (y as u256);
    vm := Bytecode.Push1(vm,0);
    vm := Bytecode.MStore(vm);
    vm := Bytecode.Push1(vm,0x1);
    vm := Bytecode.Push1(vm,0x1F);
    vm := Bytecode.Return (vm);
    Foo(x, y);
    //
    return Bytes.ReadUint8(vm.data,0), false;
  }
}

lemma Foo(x:u8, y:u8)
  ensures y <= x ==> x - y <= x
{

}
