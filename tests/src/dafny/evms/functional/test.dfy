

include "../../../../../src/dafny/evms/functional/evm.dfy"

import opened Int
import opened EVM

// Arbitrary limit for now
const GASLIMIT : nat := 100;

// Check most simple program possible
method test_01(x: u8)
requires x > 1
{
  // Initialise EVM
  var vm := EVM.create(Context.Context(0, 0, 0, []), map[], GASLIMIT,[PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  // PUSH1 x
  vm := unwrap(EVM.execute(vm));
  // PUSH1 0x2
  vm := unwrap(EVM.execute(vm));
  // MSTORE
  vm := unwrap(EVM.execute(vm));
  // PUSH
  vm := unwrap(EVM.execute(vm));
  // PUSH
  vm := unwrap(EVM.execute(vm));
  // RETURN
  var r := EVM.execute(vm);
  //
  assert data(r) == [x];
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
