include "evm.dfy"

import opened Int
import opened EVM

// Check most simple program possible
method test_01(gas: nat) returns (returndata: seq<u8>)
ensures |returndata| == 0x20
ensures Int.read_u8(returndata,0) == 0x7b {
  // Initialise EVM
  var vm := EVM.create(map[],gas,[PUSH1, 0x7b, PUSH1, 0x00, MSTORE8, PUSH1, 0x20, PUSH1, 0x00, RETURN]);
  // PUSH1 0x7b
  vm := unwrap(EVM.execute(vm));
  // PUSH1 0x00
  vm := unwrap(EVM.execute(vm));
  // MSTORE
  vm := unwrap(EVM.execute(vm));
  // PUSH1 0x20
  vm := unwrap(EVM.execute(vm));
  // PUSH1 0x00
  vm := unwrap(EVM.execute(vm));
  // RETURN
  var r := EVM.execute(vm);
  // Done
  return data(r);
}

/**
 * Unwrap an EVM result on the assumption that it should be OK
 * (i.e. not a REVERT or similar).
 */
function method unwrap(r:EVM.Result) : EVM.T
  requires r.OK?{
    var OK(v) := r;
    v
}

/**
 * Extract the return data from an EVM Result
 */
function method data(r:EVM.Result) : seq<u8>
  requires r.RETURNS? {
    var RETURNS(gas,data) := r;
    data
}
