include "evm.dfy"

import opened Int
import opened EVM

// Check most simple program possible
method test_01() {
  // Initialise SVM
  var vm := create(map[],[PUSH1,0x80]);
  // Execute program
  vm := unwrap(execute(vm));
  // Check what we know
  assert operands(vm) == 1;
  assert vm.pc == 2;
  assert peek(vm,0) == 0x80;
}

/**
 * Unwrap an EVM result on the assumption that it should be OK
 * (i.e. not a REVERT or similar).
 */
function method unwrap(r:EVM.Result) : EVM.T
  requires r.OK?{
  var OK(v) := r; v
}
