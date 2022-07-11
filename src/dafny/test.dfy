include "evm.dfy"

import opened Int
import opened EVM

// Arbitrary limit for now
const GASLIMIT : nat := 100;

// Check most simple program possible
method test_01(x: u8)
{
  // Initialise EVM
  var vm := EVM.create(map[],GASLIMIT,[PUSH1, x, PUSH1, 0x1, ADD]);
  // PUSH1
  vm := unwrap(EVM.execute(vm));
  // PUSH1
  vm := unwrap(EVM.execute(vm));
  // ADD
  vm := unwrap(EVM.execute(vm));
  assert vm.pc == 5;
  //
  assert EVM.peek(vm,0) == (x as u256) + 1;
}

/**
 * Unwrap an EVM result on the assumption that it should be OK
 * (i.e. not a REVERT or similar).
 */
function method unwrap(r:EVM.Result) : EVM.T
  requires r.OK?{
    var OK(evm) := r;
    evm
}

/**
 * Extract the return data from an EVM Result
 */
function method data(r:EVM.Result) : seq<u8>
  requires r.RETURNS? {
    var RETURNS(gas,data) := r;
    data
}
