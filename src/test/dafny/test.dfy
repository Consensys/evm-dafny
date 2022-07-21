include "../../dafny/evm.dfy"

import opened Int
import opened EVM

// Arbitrary limit for now
const GASLIMIT : nat := 100;

// Check most simple program possible
method test_execute_01(x: u8)
requires x > 1
{
  // Initialise EVM
  var tx := Context.create(0xabcd,[]);
  var vm := EVM.create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  // PUSH1 x
  vm := EVM.execute(vm);
  // PUSH1 0x2
  vm := EVM.execute(vm);
  // MSTORE
  vm := EVM.execute(vm);
  // PUSH
  vm := EVM.execute(vm);
  // PUSH
  vm := EVM.execute(vm);
  // RETURN
  vm := EVM.execute(vm);
  //
  assert vm.data == [x];
}

// ===========================================================================
// Straightline Tests
// ===========================================================================

// Write parameter into return data
method test_basic_01(x: u8)
requires x > 1
{
  var tx := Context.create(0xabcd,[]);
  var vm := EVM.create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  //
  vm := EVM.Push1(vm,x);
  vm := EVM.Push1(vm,0);
  vm := EVM.MStore(vm);
  vm := EVM.Push1(vm,0x1);
  vm := EVM.Push1(vm,0x1F);
  vm := EVM.Return(vm);
  //
  assert vm.data  == [x];
}

// Add two values and return
method test_basic_02(x: u8, y: u8) returns (z:u16)
ensures z == (x as u16) + (y as u16)
{
  var tx := Context.create(0xabcd,[]);
  var vm := EVM.create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, y, ADD, PUSH1, 0x0, MSTORE, PUSH1, 0x2, PUSH1, 0x1E, RETURN]);
  //
  vm := EVM.Push1(vm,x);
  vm := EVM.Push1(vm,y);
  vm := EVM.Add(vm);
  assert EVM.peek(vm.evm,0) == (x as u256) + (y as u256);
  vm := EVM.Push1(vm,0);
  vm := EVM.MStore(vm);
  vm := EVM.Push1(vm,0x2);
  vm := EVM.Push1(vm,0x1E);
  vm := EVM.Return(vm);
  //
  return Bytes.read_u16(vm.data,0);
}

method test_basic_03(x: u8, y: u8) returns (z:u8)
requires x >= y
ensures z <= x
{
  var tx := Context.create(0xabcd,[]);
  var vm := EVM.create(tx,map[],GASLIMIT,[PUSH1, y, PUSH1, x, SUB, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  //
  vm := EVM.Push1(vm,y);
  vm := EVM.Push1(vm,x);
  vm := EVM.Sub(vm); // x - y
  vm := EVM.Push1(vm,0);
  vm := EVM.MStore(vm);
  vm := EVM.Push1(vm,0x1);
  vm := EVM.Push1(vm,0x1F);
  vm := EVM.Return(vm);
  //
  return Bytes.read_u8(vm.data,0);
}

// ===========================================================================
// Branching Tests
// ===========================================================================

// This is an underflow test.  Either the contract reverts, or there was no underflow.
method test_branch_01(x: u8, y: u8) returns (z:u8, revert:bool)
  // Check revert only when overflow would have occurred.
  ensures revert ==> y > x
  // If didn't revert, then result is less.
  ensures !revert ==> (z <= x)
{
  var tx := Context.create(0xabcd,[]);
  var vm := EVM.create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, y, GT, ISZERO, PUSH1, 0x0A, JUMPI, REVERT, JUMPDEST, PUSH1, x, PUSH1, y, SUB, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  //
  vm := EVM.Push1(vm,x);   // 0x00
  vm := EVM.Push1(vm,y);   // 0x02
  vm := EVM.Gt(vm);        // 0x04
  vm := EVM.IsZero(vm);    // 0x05
  vm := EVM.Push1(vm,0xA); // 0x06
  vm := EVM.JumpI(vm);     // 0x08
  //
  if vm.evm.pc == 0x09 {
    vm := EVM.Revert(vm);  // 0x09
    return 0,true;
  } else {
    // Happy path
    vm := EVM.JumpDest(vm); // 0xA
    assert x >= y;
    vm := EVM.Push1(vm,y);
    vm := EVM.Push1(vm,x);
    vm := EVM.Sub(vm); // x - y
    vm := EVM.Push1(vm,0);
    vm := EVM.MStore(vm);
    vm := EVM.Push1(vm,0x1);
    vm := EVM.Push1(vm,0x1F);
    vm := EVM.Return (vm);
    //
    return Bytes.read_u8(vm.data,0), false;
  }
}

// ===========================================================================
// Looping Tests
// ===========================================================================
