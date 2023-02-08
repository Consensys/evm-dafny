include "../../../dafny/evm.dfy"
include "../../../dafny/evms/berlin.dfy"

import opened EvmState
import opened Code
import opened Int
// Some simple sanity tests to check equivalence of Push bytecodes.

method test_1(s1: ExecutingState, k:u8)
requires s1.CodeOperands() >= 1
requires DecodeUint8(s1.evm.code,s1.evm.pc+1) == k {
    var s2 := Bytecode.Push1(s1,k);
    var s3 := Bytecode.Push(s1,1);
    // Should be identical
    assert s2 == s3;
}

method test_2(s1: ExecutingState, k:u16)
requires s1.CodeOperands() >= 2
requires Bytes.ReadUint16(s1.evm.code.contents,s1.evm.pc+1) == k {
    var s2 := Bytecode.Push2(s1,k);
    var s3 := Bytecode.Push(s1,2);
    // Should be identical
    assert s2 == s3;
}
