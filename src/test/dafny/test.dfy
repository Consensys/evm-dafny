include "../../dafny/evm.dfy"

import opened Int
import opened EVM

// Arbitrary limit for now
const GASLIMIT : nat := 100;

// Check most simple program possible
method test_01(x: u8)
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
  var r := EVM.execute(vm);
  //
  assert data(r) == [x];
}

method test_02(x: u8)
requires x > 1
{
  // Initialise EVM
  var tx := Context.create(0xabcd,[]);
  var vm := EVM.create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  //
  vm := EVM.Push1(vm,x);
  vm := EVM.Push1(vm,0);
  vm := EVM.MStore(vm);
  vm := EVM.Push1(vm,0x1);
  vm := EVM.Push1(vm,0x1F);
  var r := EVM.Return(vm);
  //
  assert data(r) == [x];
}

method test_03(x: u8)
requires x > 1
{
  // Initialise EVM
  var tx := Context.create(0xabcd,[]);
  var vm := EVM.create(tx,map[],GASLIMIT,seq(1000, i=>nondet()));
  //
  vm := EVM.Push1(vm,x);
  vm := EVM.Push1(vm,0);
  vm := EVM.MStore(vm);
  vm := EVM.Push1(vm,0x1);
  vm := EVM.Push1(vm,0x1F);
  var r := EVM.Return(vm);
  //
  assert data(r) == [x];
}

/**
 * Extract the return data from an EVM Result
 */
function method data(r:EVM.State) : seq<u8>
  requires r.RETURNS? {
    var RETURNS(gas,data) := r;
    data
}
