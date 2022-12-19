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
    Block_0x00(st0)
}

function method {:verify true} Block_0x00(st: State): State
    requires st.OK? && st.PC() == 0x00
    requires st.evm.code == Code.Create(BYTECODE)
	requires st.WritesPermitted()
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() >= 0) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() >= 5) then INVALID(STACK_OVERFLOW)
	else 
		var st0 := Push1(st, 0x80);
		var st1 := Dup(st0,1);
		var st2 := Push1(st1, 0x40);
		var st3 := MStore(st2);
		var st4 := Push1(st3, 0x4);
		var st5 := CallDataSize(st4);
		var st6 := Lt(st5);
		var st7 := Push1(st6, 0x8f);
		var st8 := JumpI(st7);
		if st7.Peek(1) != 0 then 
			assert st8.PC() == 0x8f; 
			Block_0x8f(st8.UseGas(1))
		else 
			var st9 := Push1(st8, 0x0);
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
			var st18 := JumpI(st17);
			assert st18.OK?;
			if st17.Peek(1) != 0 then
				assert st18.PC() == 0x2b;
				Block_0x2b(st18.UseGas(1))
			else 
				var st19 := Push4(st18, 0xd4b83992); 
				var st20 := Dup(st19,2);
				var st21 := Eq(st20);
				var st22 := Push1(st21, 0x6b);
				var st23 := JumpI(st22);
				if st22.Peek(1) != 0 then 
					assert st23.PC() == 0x6b;
					Block_0x6b(st23.UseGas(1))
				else 
					var st24 := Push1(st23, 0x8c);
					var st25 := Jump(st24);
					assert st25.PC() == 0x8c;
					Block_0x8c(st25.UseGas(1))
}

/** Extend gas function to INVALID. */
function method EGas(st: State): nat
{
    if !st.INVALID? then st.Gas() 
    else 0
}

/**
 *  Dispatch to a target, must a jumdest 
 */
function method {:verify true} Dispatch(st: State, pc: nat := 0 ): (st': State)
    requires st.OK? 
    requires st.evm.code == Code.Create(BYTECODE)
    decreases EGas(st)
{
    if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
    else if st.PC() == 0x2b then Block_0x2b(st.UseGas(1))
    else if st.PC() == 0x34 then Block_0x34(st.UseGas(1))
    else if st.PC() == 0x44 then Block_0x44(st.UseGas(1))
    else if st.PC() == 0x5a then Block_0x5a(st.UseGas(1))
    else if st.PC() == 0x64 then Block_0x64(st.UseGas(1))
    else if st.PC() == 0x6b then Block_0x6b(st.UseGas(1))
    else if st.PC() == 0x74 then Block_0x74(st.UseGas(1))
    else if st.PC() == 0x83 then Block_0x83(st.UseGas(1))
    else if st.PC() == 0x8c then Block_0x8c(st.UseGas(1))
    else if st.PC() == 0x8f then Block_0x8f(st.UseGas(1))
    else INVALID(INVALID_JUMPDEST)
}

function method {:verify true} Block_0x2b(st: State): (st': State)
    requires st.OK? && st.PC() == 0x2b
    requires st.evm.code == Code.Create(BYTECODE)
    decreases EGas(st)
{
    if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() > 1) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() > 2) then INVALID(STACK_OVERFLOW)
    else 
        var st0 := JumpDest(st);
        var st1 := CallValue(st0);
        var st2 := IsZero(st1);
        var st3 := Push1(st2, 0x34);
        var st4 := JumpI(st3);
        if st3.Peek(1) != 0 then 
			assert st4.PC() == 0x34;
            // Dispatch(st4.UseGas(1))
			Block_0x34(st4.UseGas(1))
        else
            var st5 := Dup(st4,2);
            var st6 := Dup(st5,3);
            Revert(st6)
}

function method {:verify true} Block_0x34(st: State): (st': State)
    requires st.OK? && st.PC() == 0x34
    requires st.evm.code == Code.Create(BYTECODE)
    decreases EGas(st)
{
    if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() > 1) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() > 2) then INVALID(STACK_OVERFLOW) 
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
			assert st9.PC() == 0x44;
			Block_0x44(st9.UseGas(1))
            // Dispatch(st8.UseGas(1))
        else 
            var st10 := Dup(st9,2);
            var st11 := Dup(st10,3);
            Revert(st11)
}

function method {:verify true} Block_0x44(st: State): State
    requires st.OK? && st.PC() == 0x44
    requires st.evm.code == Code.Create(BYTECODE)
	decreases EGas(st)
{
    if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() >= 2) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() > 4) then INVALID(STACK_OVERFLOW) 
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
			assert st8.PC() == 0x5a;
			Block_0x5a(st8.UseGas(1))
            // Dispatch(st8.UseGas(1))
        else 
            var st9 := Dup(st7,3);
            var st10 := Dup(st9,4);
            Revert(st10)
}

function method {:verify true} Block_0x5a(st: State): State
    requires st.OK? && st.PC() == 0x5a
    requires st.evm.code == Code.Create(BYTECODE)
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() >= 3) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() > 1) then INVALID(STACK_OVERFLOW) 
	else
	    var st0 := JumpDest(st);
		var st1 := Dup(st0,3);
		var st2 := SLoad(st1);
		var st3 := IsZero(st2);
		var st4 := Push1(st3, 0x64);
		var tmp96 := st.Peek(1);
		var st5 := JumpI(st4);
		if st4.Peek(1) != 0 then
			assert st5.PC() == 0x64;
			Block_0x64(st5.UseGas(1))
			// Dispatch(st5.UseGas(1))
		else 
			var st6 := Dup(st5,3);
			var st7 := Dup(st6,4);
			Revert(st7)
}

function method {:verify true} Block_0x64(st: State): State
    requires st.OK? && st.PC() == 0x64
    requires st.evm.code == Code.Create(BYTECODE)
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() > 2) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() >= 2) then INVALID(STACK_OVERFLOW) 
    else 
		var st0 := JumpDest(st);
		var st1 := Dup(st0,1);
		var st2 := Dup(st1,4);
		var st3 := SStore(st2);
		assume st3.OK?;
		var st4 := Dup(st3,3);
		var st5 := Dup(st4,4);
		Return(st5)
}

function method {:verify true} Block_0x6b(st: State): State
    requires st.OK? && st.PC() == 0x6b
    requires st.evm.code == Code.Create(BYTECODE)
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() >= 3) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() > 2) then INVALID(STACK_OVERFLOW) 
    else 
		var st0 := JumpDest(st);
		var st1 := Dup(st0,1);
		var st2 := Dup(st1,4);
		var st3 := SStore(st2);
		assume st3.OK?;
		var st4 := Dup(st3,3);
		var st5 := Dup(st4,4);
		Return(st5)
}

function method {:verify true} Block_0x74(st: State): State
    requires st.OK? && st.PC() == 0x74
    requires st.evm.code == Code.Create(BYTECODE)
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() >= 3) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() > 2) then INVALID(STACK_OVERFLOW) 
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
			assert st9.PC() == 0x83;
			Block_0x83(st9.UseGas(1))
			// Dispatch(st9.UseGas(1))
		else 
			var st10 := Dup(st9,2);
			var st11 := Dup(st10,3);
			Revert(st11)
}

function method {:verify true} Block_0x83(st: State): State
    requires st.OK? && st.PC() == 0x83
    requires st.evm.code == Code.Create(BYTECODE)
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() >= 3) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() > 1) then INVALID(STACK_OVERFLOW) 
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

function method {:verify true} Block_0x8c(st: State): State
    requires st.OK? && st.PC() == 0x8c
    requires st.evm.code == Code.Create(BYTECODE)
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() >= 3) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() > 1) then INVALID(STACK_OVERFLOW) 
    else 
		var st0 := JumpDest(st);
		var st1 := Pop(st0);
		Pop(st1)
}

function method {:verify true} Block_0x8f(st: State): State
    requires st.OK? && st.PC() == 0x8f
    requires st.evm.code == Code.Create(BYTECODE)
	decreases EGas(st)
{
	if st.Gas() < 1 then INVALID(INSUFFICIENT_GAS)
	else if !(st.Operands() >= 0) then INVALID(STACK_UNDERFLOW)
	else if !(st.Capacity() > 1) then INVALID(STACK_OVERFLOW) 
    else 
		var st0 := JumpDest(st);
		var st1 := Push1(st0, 0x0);
		var st2 := Dup(st1,1);
		Revert(st2)
}

/* 
method main(context: Context.T, world: map<u160,WorldState.Account>, gas: nat)
requires context.writePermission
requires gas > 100000
requires context.address in world {
	var st := EvmBerlin.Create(context,world,gas,BYTECODE);
	st := Push1(st, 0x80);
	st := Dup(st,1);
	st := Push1(st, 0x40);
	st := MStore(st);
	st := Push1(st, 0x4);
	st := CallDataSize(st);
	st := Lt(st);
	st := Push1(st, 0x8f);
	var tmp12 := st.Peek(1);
	st := JumpI(st);
	if tmp12 != 0 { block_0x8f(st); return; }
    assert st.Capacity() > 6;
    block_0xd(st);
}

method block_0xd(st': State)
requires st'.OK? && st'.PC() == 0xd
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.WritesPermitted()
requires st'.Operands() >= 1 && st'.Capacity() > 10 {
    var st := st';
	st := Push1(st, 0x0);
	st := Dup(st,1);
	st := CallDataLoad(st);
	st := Push1(st, 0xe0);
	st := Shr(st);
	st := Push4(st, 0x310bd74b);
	st := Dup(st,2);
	st := Eq(st);
	st := Push1(st, 0x2b);
	var tmp29 := st.Peek(1);
    assume BYTECODE[0x2b] == JUMPDEST;
	st := JumpI(st);
	if tmp29 != 0 { block_0x2b(st); return; }
    block_0x1e(st);
}

method block_0x1e(st': State)
requires st'.OK? && st'.PC() == 0x1e
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.WritesPermitted()
requires st'.Operands() >= 3 && st'.Capacity() > 2 {
    var st := JumpDest(st');
	st := Push4(st, 0xd4b83992);
	st := Dup(st,2);
	st := Eq(st);
	st := Push1(st, 0x6b);
	var tmp39 := st.Peek(1);
	st := JumpI(st);
	if tmp39 != 0 { block_0x6b(st); return; }
	st := Push1(st, 0x8c);
	st := Jump(st);
	// block_0x8c(st);
}

method block_0x2b(st': State)
requires st'.OK? && st'.PC() == 0x2b
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.WritesPermitted()
requires st'.Operands() > 1 && st'.Capacity() > 2 {
	var st := JumpDest(st');
	st := CallValue(st);
	st := IsZero(st);
	st := Push1(st, 0x34);
	var tmp48 := st.Peek(1);
	st := JumpI(st);
	if tmp48 != 0 { block_0x34(st); return; }
	st := Dup(st,2);
	st := Dup(st,3);
	st := Revert(st);
}

method block_0x34(st': State)
requires st'.OK? && st'.PC() == 0x34
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.WritesPermitted()
requires st'.Operands() > 1 && st'.Capacity() > 2 {
	var st := JumpDest(st');
	st := Push1(st, 0x20);
	st := Push1(st, 0x3);
	st := Not(st);
	st := CallDataSize(st);
	st := Add(st);
	st := SLt(st);
	st := IsZero(st);
	st := Push1(st, 0x44);
	var tmp64 := st.Peek(1);
	st := JumpI(st);
	if tmp64 != 0 { block_0x44(st); return; }
	st := Dup(st,2);
	st := Dup(st,3);
	st := Revert(st);
}

method block_0x44(st': State)
requires st'.OK? && st'.PC() == 0x44
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.WritesPermitted()
requires st'.Operands() >= 2 && st'.Capacity() > 2 {
	var st := JumpDest(st');
	st := Push1(st, 0x4);
	st := CallDataLoad(st);
	st := Push8(st, 0xde0b6b3a7640000);
	st := Dup(st,2);
	st := Gt(st);
	st := IsZero(st);
	st := Push1(st, 0x5a);
	var tmp86 := st.Peek(1);
	st := JumpI(st);
	if tmp86 != 0 { block_0x5a(st); return; }
	st := Dup(st,3);
	st := Dup(st,4);
	st := Revert(st);
}

method block_0x5a(st': State)
requires st'.OK? && st'.PC() == 0x5a
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.WritesPermitted()
requires st'.Operands() >= 3 && st'.Capacity() > 1 {
	var st := JumpDest(st');
	st := Dup(st,3);
	st := SLoad(st);
	st := IsZero(st);
	st := Push1(st, 0x64);
	var tmp96 := st.Peek(1);
	st := JumpI(st);
	if tmp96 != 0 { block_0x64(st); return; }
	st := Dup(st,3);
	st := Dup(st,4);
	st := Revert(st);
}

method block_0x64(st': State)
requires st'.OK? && st'.PC() == 0x64
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.WritesPermitted()
requires st'.Operands() > 2 && st'.Capacity() >= 2 {
	var st := JumpDest(st');
	st := Dup(st,1);
	st := Dup(st,4);
	st := SStore(st);
	st := Dup(st,3);
	st := Dup(st,4);
	st := Return(st);
}

method block_0x6b(st': State)
requires st'.OK? && st'.PC() == 0x6b
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.Operands() >= 3 && st'.Capacity() > 2 {
	var st := JumpDest(st');
	st := CallValue(st);
	st := IsZero(st);
	st := Push1(st, 0x74);
	var tmp112 := st.Peek(1);
	st := JumpI(st);
	if tmp112 != 0 { block_0x74(st); return; }
	st := Dup(st,2);
	st := Dup(st,3);
	st := Revert(st);
}

method block_0x74(st': State)
requires st'.OK? && st'.PC() == 0x74
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.Operands() >= 3 && st'.Capacity() > 2 {
	var st := JumpDest(st');
	st := Dup(st,2);
	st := Push1(st, 0x3);
	st := Not(st);
	st := CallDataSize(st);
	st := Add(st);
	st := SLt(st);
	st := IsZero(st);
	st := Push1(st, 0x83);
	var tmp127 := st.Peek(1);
	st := JumpI(st);
	if tmp127 != 0 { block_0x83(st); return; }
	st := Dup(st,2);
	st := Dup(st,3);
	st := Revert(st);
}

method block_0x83(st': State)
requires st'.OK? && st'.PC() == 0x83
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.Operands() >= 3 && st'.Capacity() > 1 {
	var st := JumpDest(st');
	st := Dup(st,2);
	st := SLoad(st);
	st := Dup(st,4);
	st := MStore(st);
	st := Push1(st, 0x20);
	st := Dup(st,4);
	st := Return(st);
}

method block_0x8c(st': State)
requires st'.OK? && st'.PC() == 0x8c
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.Operands() >= 2 && st'.Capacity() > 0 {
	var st := JumpDest(st');
	st := Pop(st);
	st := Pop(st);
}

method block_0x8f(st': State)
requires st'.OK? && st'.PC() == 0x8f
requires st'.evm.code == Code.Create(BYTECODE)
requires st'.Operands() >= 0 && st'.Capacity() > 1 {
	var st := JumpDest(st');
	st := Push1(st, 0x0);
	st := Dup(st,1);
	st := Revert(st);
}


*/