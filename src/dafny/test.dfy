include "evm.dfy"

import opened Int
import opened EVM

// Check most simple program possible
method test_01(gas: nat) returns (returndata: seq<u8>)
//ensures |returndata| > 31
//ensures Int.read_u8(returndata,31) == 0x7b
{
  // Initialise EVM
  var vm := EVM.create(map[],gas,[PUSH1, 0x7b, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN]);
  // PUSH1 0x7b
  vm := unwrap(EVM.execute(vm));
  // PUSH1 0x00
  vm := unwrap(EVM.execute(vm));
  // MSTORE
  vm := unwrap(EVM.execute(vm));
  assert vm.pc == 5;
  // PUSH1 0x20
  vm := unwrap(EVM.execute(vm));
  assert vm.pc == 7;
  assert EVM.peek(vm,0) == 32;
  // PUSH1 0x00
  vm := unwrap(EVM.execute(vm));
  assert vm.pc == 9;
  assert EVM.peek(vm,0) == 0;
  assert EVM.peek(vm,1) == 32;
  // RETURN
  var r := EVM.execute(vm);
  // // Done
  var data := data(r);
  assert |data| > 8;
  return [];
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
