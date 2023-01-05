include "../../dafny/evm.dfy"
include "../../dafny/evms/berlin.dfy"

import opened Int
import opened Opcode
import opened Memory
import opened Bytecode
import opened EvmBerlin
import opened EvmState

const BYTECODE : seq<u8> := [
    PUSH1, 0x80, // 0x0
	DUP1,  // 0x2
	PUSH1, 0x40, // 0x3
	MSTORE,  // 0x5
	PUSH1, 0x4, // 0x6
	CALLDATASIZE,  // 0x8
	LT,  // 0x9
	PUSH1, 0x8f, // 0xa
	JUMPI,  // 0xc
	PUSH1, 0x0, // 0xd
	DUP1,  // 0xf
	CALLDATALOAD,  // 0x10
	PUSH1, 0xe0, // 0x11
	SHR,  // 0x13
	PUSH4, 0x31,0xb,0xd7,0x4b, // 0x14
	DUP2,  // 0x19
	EQ,  // 0x1a
	PUSH1, 0x2b, // 0x1b
	JUMPI,  // 0x1d
	PUSH4, 0xd4,0xb8,0x39,0x92, // 0x1e
	DUP2,  // 0x23
	EQ,  // 0x24
	PUSH1, 0x6b, // 0x25
	JUMPI,  // 0x27
	PUSH1, 0x8c, // 0x28
	JUMP,  // 0x2a

	JUMPDEST,  // 0x2b
	CALLVALUE,  // 0x2c
	ISZERO,  // 0x2d
	PUSH1, 0x34, // 0x2e
	JUMPI,  // 0x30
	DUP2,  // 0x31
	DUP3,  // 0x32
	REVERT,  // 0x33

	JUMPDEST,  // 0x34
	PUSH1, 0x20, // 0x35
	PUSH1, 0x3, // 0x37
	NOT,  // 0x39
	CALLDATASIZE,  // 0x3a
	ADD,  // 0x3b
	SLT,  // 0x3c
	ISZERO,  // 0x3d
	PUSH1, 0x44, // 0x3e
	JUMPI,  // 0x40
	DUP2,  // 0x41
	DUP3,  // 0x42
	REVERT,  // 0x43

	JUMPDEST,  // 0x44
	PUSH1, 0x4, // 0x45
	CALLDATALOAD,  // 0x47
	PUSH8, 0xd,0xe0,0xb6,0xb3,0xa7,0x64,0x0,0x0, // 0x48
	DUP2,  // 0x51
	GT,  // 0x52
	ISZERO,  // 0x53
	PUSH1, 0x5a, // 0x54
	JUMPI,  // 0x56
	DUP3,  // 0x57
	DUP4,  // 0x58
	REVERT,  // 0x59

	JUMPDEST,  // 0x5a
	DUP3,  // 0x5b
	SLOAD,  // 0x5c
	ISZERO,  // 0x5d
	PUSH1, 0x64, // 0x5e
	JUMPI,  // 0x60
	DUP3,  // 0x61
	DUP4,  // 0x62
	REVERT,  // 0x63

	JUMPDEST,  // 0x64
	DUP1,  // 0x65
	DUP4,  // 0x66
	SSTORE,  // 0x67
	DUP3,  // 0x68
	DUP4,  // 0x69
	RETURN,  // 0x6a

	JUMPDEST,  // 0x6b
	CALLVALUE,  // 0x6c
	ISZERO,  // 0x6d
	PUSH1, 0x74, // 0x6e
	JUMPI,  // 0x70
	DUP2,  // 0x71
	DUP3,  // 0x72
	REVERT,  // 0x73

	JUMPDEST,  // 0x74
	DUP2,  // 0x75
	PUSH1, 0x3, // 0x76
	NOT,  // 0x78
	CALLDATASIZE,  // 0x79
	ADD,  // 0x7a
	SLT,  // 0x7b
	ISZERO,  // 0x7c
	PUSH1, 0x83, // 0x7d
	JUMPI,  // 0x7f
	DUP2,  // 0x80
	DUP3,  // 0x81
	REVERT,  // 0x82

	JUMPDEST,  // 0x83
	DUP2,  // 0x84
	SLOAD,  // 0x85
	DUP4,  // 0x86
	MSTORE,  // 0x87
	PUSH1, 0x20, // 0x88
	DUP4,  // 0x8a
	RETURN,  // 0x8b

	JUMPDEST,  // 0x8c
	POP,  // 0x8d
	POP,  // 0x8e

	JUMPDEST,  // 0x8f
	PUSH1, 0x0, // 0x90
	DUP1,  // 0x92
	REVERT // 0x93
];

lemma SanityCheck()
	ensures BYTECODE[0x2b] == JUMPDEST

// Code for each block [jumpdest or pc = 0]

function method Main(context: Context.T, world: map<u160,WorldState.Account>, gas: nat): State
{
    var st0 := EvmBerlin.InitEmpty(gas, BYTECODE);
	assert st0.WritesPermitted();
    Block_0x00(st0)
}

function method Block_0x00_a(st: State): (st': State)
	requires st.OK? && st.PC() == 0x00
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 0
	requires st.Capacity() >= 4
	requires st.WritesPermitted()
{
	var st0 := Push1(st, 0x80);
	var st1 := Dup(st0,1);
	var st2 := Push1(st1, 0x40);
	var st3 := MStore(st2);
	var st4 := Push1(st3, 0x4);
	var st5 := CallDataSize(st4);
	var st6 := Lt(st5);
	var st7 := Push1(st6, 0x8f);
	st7
}

function method Block_0x00_b(st: State): (st': State)
	requires st.OK? && st.PC() == 0x0d
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 0
	requires st.Capacity() >= 4
{
	var st9 := Push1(st, 0x0);
	var st10 := Dup(st9,1);
	var st11 := CallDataLoad(st10);
	var st12 := Push1(st11, 0xe0);
	var st13 := Shr(st12);
	var st14 := Push4(st13, 0x310bd74b);
	var st15 := Dup(st14,2);
	var st16 := Eq(st15);
	var st17 := Push1(st16, 0x2b);
	SanityCheck();
	assert BYTECODE[0x2b] == JUMPDEST;
	st17
}

function method Block_0x00_c(st: State): (st': State)
	requires st.OK? && st.PC() == 0x1e
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 1
	requires st.Capacity() >= 2
{
	var st19 := Push4(st, 0xd4b83992); 
	var st20 := Dup(st19,2);
	var st21 := Eq(st20);
	var st22 := Push1(st21, 0x6b); 
	st22
}

function method {:verify true} Block_0x00(st: State): (st': State)
    requires st.OK? && st.PC() == 0x00
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 0
	requires st.Capacity() >= 8
	requires st.WritesPermitted()
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else 
		var st7 := Block_0x00_a(st);
		var st8 := JumpI(st7);
		if st7.Peek(1) != 0 then 
			Block_0x8f(st8.UseGas(1))
		else 
			var st17 := Block_0x00_b(st8);
			SanityCheck();
			assert BYTECODE[0x2b] == JUMPDEST;
			var st18 := JumpI(st17);
			if st17.Peek(1) != 0 then
				Block_0x2b(st18.UseGas(1))
			else 
				var st19 := Push4(st18, 0xd4b83992); 
				var st20 := Dup(st19,2);
				var st21 := Eq(st20);
				var st22 := Push1(st21, 0x6b);
				var st23 := JumpI(st22);
				if st22.Peek(1) != 0 then 
					Block_0x6b(st23.UseGas(1))
				else 
					var st24 := Push1(st23, 0x8c);
					var st25 := Jump(st24);
					Block_0x8c(st25.UseGas(1))
}

/** Extend gas function to INVALID. */
function method EGas(st: State): nat
{
    if !st.INVALID? then st.Gas() 
    else 0
}

function method {:verify true} Block_0x2b(st: State): (st': State)
    requires st.OK? && st.PC() == 0x2b
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() > 1 && st.Capacity() > 4
	requires st.WritesPermitted()
    decreases EGas(st)
{
    if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
    else 
        var st0 := JumpDest(st);
        var st1 := CallValue(st0);
        var st2 := IsZero(st1);
        var st3 := Push1(st2, 0x34);
        var st4 := JumpI(st3);
        if st3.Peek(1) != 0 then 
			Block_0x34(st4.UseGas(1))
        else
            var st5 := Dup(st4,2);
            var st6 := Dup(st5,3);
            Revert(st6)
}

function method {:verify true} Block_0x34(st: State): (st': State)
    requires st.OK? && st.PC() == 0x34
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() > 1 && st.Capacity() > 4
	requires st.WritesPermitted()
    decreases EGas(st)
{
    if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else 
        var st0 := JumpDest(st);
        var st1 := Push1(st0, 0x20);
        var st2 := Push1(st1, 0x3);
        var st3 := Not(st2);
        var st4 := CallDataSize(st3);
        var st5 := Add(st4);
        var st6 := SLt(st5);
        var st7 := IsZero(st6);
        var st8 := Push1(st7, 0x44);
        var st9 := JumpI(st8);
        if st8.Peek(1) != 0 then
			Block_0x44(st9.UseGas(1))
        else 
            var st10 := Dup(st9,2);
            var st11 := Dup(st10,3);
            Revert(st11)
}

function method {:verify true} Block_0x44(st: State): (st': State)
    requires st.OK? && st.PC() == 0x44
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 2 && st.Capacity() > 4
	requires st.WritesPermitted()
	decreases EGas(st)
{
    if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
    else
        var st0 := JumpDest(st);
        var st1 := Push1(st0, 0x4);
        var st2 := CallDataLoad(st1);
        var st3 := Push8(st2, 0xde0b6b3a7640000); 
        var st4 := Dup(st3,2);
        var st5 := Gt(st4);
        var st6 := IsZero(st5);
        var st7 := Push1(st6, 0x5a);
        var st8 := JumpI(st7);
        if st7.Peek(1) != 0 then 
			Block_0x5a(st8.UseGas(1))
        else 
            var st9 := Dup(st7,3);
            var st10 := Dup(st9,4);
            Revert(st10)
}

function method {:verify true} Block_0x5a(st: State): (st': State)
    requires st.OK? && st.PC() == 0x5a
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 3 && st.Capacity() > 1
	requires st.WritesPermitted()
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else
	    var st0 := JumpDest(st);
		var st1 := Dup(st0,3);
		var st2 := SLoad(st1);
		var st3 := IsZero(st2);
		var st4 := Push1(st3, 0x64);
		var tmp96 := st.Peek(1);
		var st5 := JumpI(st4);
		if st4.Peek(1) != 0 then
			assume st5.Capacity() >= 2;
			Block_0x64(st5.UseGas(1))
		else 
			var st6 := Dup(st5,3);
			var st7 := Dup(st6,4);
			Revert(st7)
}

function method {:verify true} Block_0x64(st: State): (st': State)
    requires st.OK? && st.PC() == 0x64
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() > 2 && st.Capacity() >= 2
	requires st.WritesPermitted()
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
    else 
		var st0 := JumpDest(st);
		var st1 := Dup(st0,1);
		var st2 := Dup(st1,4);
		var st3 := SStore(st2);
		var st4 := Dup(st3,3);
		var st5 := Dup(st4,4);
		Return(st5)
}

function method {:verify true} Block_0x6b(st: State): (st': State)
    requires st.OK? && st.PC() == 0x6b
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 3 && st.Capacity() > 2
	requires st.WritesPermitted()
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
    else 
		var st0 := JumpDest(st);
		var st1 := Dup(st0,1);
		var st2 := Dup(st1,4);
		var st3 := SStore(st2);
		// assume st3.OK?;
		var st4 := Dup(st3,3);
		var st5 := Dup(st4,4);
		Return(st5)
}

function method {:verify true} Block_0x74(st: State): (st': State)
    requires st.OK? && st.PC() == 0x74
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 3 && st.Capacity() > 2
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
    else 
		var st0 := JumpDest(st);
		var st1 := Dup(st0,2);
		var st2 := Push1(st1, 0x3);
		var st3 := Not(st2);
		var st4 := CallDataSize(st3);
		var st5 := Add(st4);
		var st6 := SLt(st5);
		var st7 := IsZero(st6);
		var st8 := Push1(st7, 0x83);
		var st9 := JumpI(st8);
		if st8.Peek(1) != 0 then
			Block_0x83(st9.UseGas(1))
		else 
			var st10 := Dup(st9,2);
			var st11 := Dup(st10,3);
			Revert(st11)
}

function method {:verify true} Block_0x83(st: State): (st': State)
    requires st.OK? && st.PC() == 0x83
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 3 && st.Capacity() > 1
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
    else 
		var st0 := JumpDest(st);
		var st1 := Dup(st0,2);
		var st2 := SLoad(st1);
		var st3 := Dup(st2,4);
		var st4 := MStore(st3);
		var st5 := Push1(st4, 0x20);
		var st6 := Dup(st5,4);
		Return(st6)
}

function method {:verify true} Block_0x8c(st: State): (st': State)
    requires st.OK? && st.PC() == 0x8c
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 2 && st.Capacity() > 1
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
    else 
		var st0 := JumpDest(st); 
		assert st0.Operands() >= 1;
		var st1 := Pop(st0);
		assert st1.Operands() >= 1;
		Pop(st1)
}

function method {:verify true} Block_0x8f(st: State): (st': State)
    requires st.OK? && st.PC() == 0x8f
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.Operands() >= 0 && st.Capacity() > 1
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
    else 
		var st0 := JumpDest(st);
		var st1 := Push1(st0, 0x0);
		var st2 := Dup(st1,1);
		Revert(st2)
}
