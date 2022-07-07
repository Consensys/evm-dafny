/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

include "util/int.dfy"
include "util/memory.dfy"
include "util/storage.dfy"
include "util/stack.dfy"
include "util/code.dfy"

/**
 * Top-level definition of an Ethereum Virtual Machine.
 */
module EVM {
  import opened Int
  import I256
  import Word
  import Stack
  import Memory
  import Storage
  import Code

  datatype T = EVM(
    stack   : Stack.T,
    memory  : Memory.T,
    storage : Storage.T,
    code: Code.T,
    gas: nat,
    pc : u256
  )

  /**
   * Create a fresh EVM to execute a given sequence of bytecode instructions.
   * The EVM is  initialised with an empty stack and empty local memory.
   */
  function method create(storage: map<u256,u256>, gas: nat, code: seq<u8>) : T
  requires |code| <= MAX_U256 {
    var stck := Stack.create();
    var mem := Memory.create();
    var sto := Storage.create(storage);
    var cod := Code.create(code);
    EVM(stack:=stck,memory:=mem,storage:=sto,code:=cod,gas:=gas,pc:=0)
  }

  // =============================================================================
  // Bytecode Semantics
  // =============================================================================

  const G_zero : int := 0;
	const G_base : int := 2;
	const G_verylow : int := 3;
	const G_low : int := 5;
	const G_mid : int := 8;
	const G_high : int := 10;
	const G_extcode : int := 700;
	const G_balance : int := 400;
	const G_sload : int := 200;
	const G_jumpdest : int := 1;
	const G_sset : int := 20000;
	const G_sreset : int := 5000;
	const R_sclear : int := 15000;
	const R_selfdestruct : int := 24000;
	const G_selfdestruct : int := 5000;
	const G_create : int := 32000;
	const G_codedeposit : int := 200;
	const G_call : int := 700;
	const G_callvalue : int := 9000;
	const G_callstipend : int := 2300;
	const G_newaccount : int := 25000;
	const G_exp : int := 10;
	const G_expbyte : int := 50;
	const G_memory : int := 3;
	const G_txcreate : int := 32000;
	const G_txdatazero : int := 4;
	const G_txdatanonzero : int := 68;
	const G_transaction : int := 21000;
	const G_log : int := 375;
	const G_logdata : int := 8;
	const G_logtopic : int := 375;
	const G_sha3 : int := 30;
	const G_sha3word : int := 6;
	const G_copy : int := 3;
	const G_blockhash : int := 20;
	const G_quaddivisor : int := 100;

	// 0s: Stop and Arithmetic Operations
	const STOP : u8 := 0x0;
	const ADD : u8 := 0x01;
	const MUL : u8 := 0x02;
	const SUB : u8 := 0x03;
	const DIV : u8 := 0x04;
	const SDIV : u8 := 0x05;
	const MOD : u8 := 0x06;
	const SMOD : u8 := 0x07;
	const ADDMOD : u8 := 0x08;
	const MULMOD : u8 := 0x09;
	const EXP : u8 := 0x0a;
	const SIGNEXTEND : u8 := 0x0b;
	// 10s: Comparison & Bitwise Logic Operations
	const LT : u8 := 0x10;
	const GT : u8 := 0x11;
	const SLT : u8 := 0x12;
	const SGT : u8 := 0x13;
	const EQ : u8 := 0x14;
	const ISZERO : u8 := 0x15;
	const AND : u8 := 0x16;
	const OR : u8 := 0x17;
	const XOR : u8 := 0x18;
	const NOT : u8 := 0x19;
	const BYTE : u8 := 0x1a;
	// 20s: SHA3
	const SHA3 : u8 := 0x20;
	// 30s: Environment Information
	const ADDRESS : u8 := 0x30;
	const BALANCE : u8 := 0x31;
	const ORIGIN : u8 := 0x32;
	const CALLER : u8 := 0x33;
	const CALLVALUE : u8 := 0x34;
	const CALLDATALOAD : u8 := 0x35;
	const CALLDATASIZE : u8 := 0x36;
	const CALLDATACOPY : u8 := 0x37;
	const CODESIZE : u8 := 0x38;
	const CODECOPY : u8 := 0x39;
	const GASPRICE : u8 := 0x3a;
	const EXTCODESIZE : u8 := 0x3b;
	const EXTCODECOPY : u8 := 0x3c;
	const RETURNDATASIZE : u8 := 0x3d;
	const RETURNDATACOPY : u8 := 0x3e;
	// 40s: Block Information
	const BLOCKHASH : u8 := 0x40;
	const COINBASE : u8 := 0x41;
	const TIMESTAMP : u8 := 0x42;
	const NUMBER : u8 := 0x43;
	const DIFFICULTY : u8 := 0x44;
	const GASLIMIT : u8 := 0x45;
	// 50s: Stack, Memory Storage and Flow Operations
	const POP : u8 := 0x50;
	const MLOAD : u8 := 0x51;
	const MSTORE : u8 := 0x52;
	const MSTORE8 : u8 := 0x53;
	const SLOAD : u8 := 0x54;
	const SSTORE : u8 := 0x55;
	const JUMP : u8 := 0x56;
	const JUMPI : u8 := 0x57;
	const PC : u8 := 0x58;
	const MSIZE : u8 := 0x59;
	const GAS : u8 := 0x5a;
	const JUMPDEST : u8 := 0x5b;
	// 60s & 70s: Push Operations
	const PUSH1 : u8 := 0x60;
	const PUSH2 : u8 := 0x61;
	const PUSH3 : u8 := 0x62;
	const PUSH4 : u8 := 0x63;
	const PUSH5 : u8 := 0x64;
	const PUSH6 : u8 := 0x65;
	const PUSH7 : u8 := 0x66;
	const PUSH8 : u8 := 0x67;
	const PUSH9 : u8 := 0x68;
	const PUSH10 : u8 := 0x69;
	const PUSH11 : u8 := 0x6a;
	const PUSH12 : u8 := 0x6b;
	const PUSH13 : u8 := 0x6c;
	const PUSH14 : u8 := 0x6d;
	const PUSH15 : u8 := 0x6e;
	const PUSH16 : u8 := 0x6f;
	const PUSH17 : u8 := 0x70;
	const PUSH18 : u8 := 0x71;
	const PUSH19 : u8 := 0x72;
	const PUSH20 : u8 := 0x73;
	const PUSH21 : u8 := 0x74;
	const PUSH22 : u8 := 0x75;
	const PUSH23 : u8 := 0x76;
	const PUSH24 : u8 := 0x77;
	const PUSH25 : u8 := 0x78;
	const PUSH26 : u8 := 0x79;
	const PUSH27 : u8 := 0x7a;
	const PUSH28 : u8 := 0x7b;
	const PUSH29 : u8 := 0x7c;
	const PUSH30 : u8 := 0x7d;
	const PUSH31 : u8 := 0x7e;
	const PUSH32 : u8 := 0x7f;
	// 80s: Duplication Operations
	const DUP1 : u8 := 0x80;
	const DUP2 : u8 := 0x81;
	const DUP3 : u8 := 0x82;
	const DUP4 : u8 := 0x83;
	const DUP5 : u8 := 0x84;
	const DUP6 : u8 := 0x85;
	const DUP7 : u8 := 0x86;
	const DUP8 : u8 := 0x87;
	const DUP9 : u8 := 0x88;
	const DUP10 : u8 := 0x89;
	const DUP11 : u8 := 0x8a;
	const DUP12 : u8 := 0x8b;
	const DUP13 : u8 := 0x8c;
	const DUP14 : u8 := 0x8d;
	const DUP15 : u8 := 0x8e;
	const DUP16 : u8 := 0x8f;
	// 90s: Exchange Operations
	const SWAP1 : u8 := 0x90;
	const SWAP2 : u8 := 0x91;
	const SWAP3 : u8 := 0x92;
	const SWAP4 : u8 := 0x93;
	const SWAP5 : u8 := 0x94;
	const SWAP6 : u8 := 0x95;
	const SWAP7 : u8 := 0x96;
	const SWAP8 : u8 := 0x97;
	const SWAP9 : u8 := 0x98;
	const SWAP10 : u8 := 0x99;
	const SWAP11 : u8 := 0x9a;
	const SWAP12 : u8 := 0x9b;
	const SWAP13 : u8 := 0x9c;
	const SWAP14 : u8 := 0x9d;
	const SWAP15 : u8 := 0x9e;
	const SWAP16 : u8 := 0x9f;
	// a0s: Logging Operations
	const LOG0 : u8 := 0xa0;
	const LOG1 : u8 := 0xa1;
	const LOG2 : u8 := 0xa2;
	const LOG3 : u8 := 0xa3;
	const LOG4 : u8 := 0xa4;
	// f0s: System operations
	const CREATE : u8 := 0xf0;
	const CALL : u8 := 0xf1;
	const CALLCODE : u8 := 0xf2;
	const RETURN : u8 := 0xf3;
	const DELEGATECALL : u8 := 0xf4;
	const STATICCALL : u8 := 0xfa;
	const REVERT : u8 := 0xfd;
	const INVALID : u8 := 0xfe;
	const SELFDESTRUCT : u8 := 0xff;

  /**
   * Captures the possible outcomes from executing a bytecode.  Normal execution is indicated
   * by OK (with the updated machine state).  An exceptional halt is indicated by INVALID
   * (e.g. insufficient gas, insufficient stack operands, etc).  Finally, a RETURN or REVERT
   * with return data are indicated accordingly (along with any gas returned).
   */
  datatype Result = OK(evm:T) | INVALID | RETURNS(gas:nat,data:seq<u8>) | REVERT(gas:nat,data:seq<u8>)

  /**
   * Execute a single step of the EVM.  This either results in a valid EVM (i.e. so execution
   * can continue), or some form of halt (e.g. exceptional, revert, etc).
   */
  function method execute(vm:T) : Result {
    // Decode
    var (vm',opcode) := decode(vm);
    // Dispatch
    if opcode == STOP then evalSTOP(vm')
    else if opcode == ADD then evalADD(vm')
    else if opcode == MUL then evalMUL(vm')
    else if opcode == SUB then evalSUB(vm')
    else if opcode == DIV then evalDIV(vm')
    else if opcode == SDIV then evalSDIV(vm')
    else if opcode == MOD then evalMOD(vm')
    else if opcode == SMOD then evalSMOD(vm')
    else if opcode == ADDMOD then evalADDMOD(vm')
    else if opcode == MULMOD then evalMULMOD(vm')
      // EXP
      // SIGNEXTEND
    // 0x10
    else if opcode == LT then evalLT(vm')
    else if opcode == GT then evalGT(vm')
    else if opcode == SLT then evalSLT(vm')
    else if opcode == SGT then evalSGT(vm')
    else if opcode == EQ then evalEQ(vm')
    else if opcode == ISZERO then evalISZERO(vm')
    else if opcode == AND then evalAND(vm')
    else if opcode == OR then evalOR(vm')
    else if opcode == XOR then evalXOR(vm')
    else if opcode == NOT then evalNOT(vm')
      // BYTE
      // SHL
      // SHR
      // SAR
    // 0x50
    else if opcode == POP then evalPOP(vm')
    else if opcode == MLOAD then evalMLOAD(vm')
    else if opcode == MSTORE then evalMSTORE(vm')
    else if opcode == MSTORE8 then evalMSTORE8(vm')
    else if opcode == SLOAD then evalSLOAD(vm')
    else if opcode == SSTORE then evalSSTORE(vm')
    // 0x60
    else if opcode == PUSH1 then evalPUSH1(vm')
    else if opcode == PUSH2 then evalPUSH2(vm')
    // 0x80
    else if DUP1 <= opcode <= DUP16 then
      var k := (opcode - DUP1) as int; evalDUP(vm',k)
    // 0x90
    else if SWAP1 <= opcode <= SWAP16 then
      var k := (opcode - SWAP1) as int; evalSWAP(vm',k+1)
    // 0xf0
    else if opcode == RETURN then evalRETURN(vm')
    else
      // Invalid opcode
      Result.INVALID
  }

  /**
   * Evaluate the STOP bytecode.  This halts the machine without
   * return output data.
   */
  function method evalSTOP(vm:T) : Result {
    Result.RETURNS(gas:=vm.gas,data:=[])
  }

  /**
   * Unsigned integer addition with modulo arithmetic.
   */
  function method evalADD(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var res := (lhs + rhs) % TWO_256;
      Result.OK(push(pop(pop(vm)),res as u256))
    else
      Result.INVALID
  }

  /**
   * Unsigned integer multiplication with modulo arithmetic.
   */
  function method evalMUL(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var res := (lhs * rhs) % TWO_256;
      Result.OK(push(pop(pop(vm)),res as u256))
    else
      Result.INVALID
  }

  /**
   * Unsigned integer subtraction with modulo arithmetic.
   */
  function method evalSUB(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var res := (lhs - rhs) % TWO_256;
      Result.OK(push(pop(pop(vm)),res as u256))
    else
      Result.INVALID
  }

  /**
   * Unsigned integer division.
   */
  function method evalDIV(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      var res := div(lhs,rhs) as u256;
      Result.OK(push(pop(pop(vm)),res))
    else
      Result.INVALID
  }

  /**
   * Signed integer division.
   */
  function method evalSDIV(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := Word.asI256(peek(vm,0));
      var rhs := Word.asI256(peek(vm,1));
      var res := Word.fromI256(sdiv(lhs,rhs));
      Result.OK(push(pop(pop(vm)),res))
    else
      Result.INVALID
  }

  /**
   * (Unsigned) Modulo remainder.
   */
  function method evalMOD(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      var res := mod(lhs,rhs) as u256;
      Result.OK(push(pop(pop(vm)),res))
    else
      Result.INVALID
  }

  /**
   * Signed integer remainder:
   */
  function method evalSMOD(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := Word.asI256(peek(vm,0));
      var rhs := Word.asI256(peek(vm,1));
      var res := Word.fromI256(smod(lhs,rhs));
      Result.OK(push(pop(pop(vm)),res))
    else
      Result.INVALID
  }

  /**
   * Unsigned integer modulo addition.
   */
  function method evalADDMOD(vm:T) : Result {
    if operands(vm) >= 3
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var rem := peek(vm,2) as int;
      var res := if rem == 0 then 0 else(lhs + rhs) % rem;
      Result.OK(push(pop(pop(vm)),res as u256))
    else
      Result.INVALID
  }

  /**
   * Unsigned integer modulo multiplication.
   */
  function method evalMULMOD(vm:T) : Result {
    if operands(vm) >= 3
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var rem := peek(vm,2) as int;
      var res := if rem == 0 then 0 else(lhs * rhs) % rem;
      Result.OK(push(pop(pop(vm)),res as u256))
    else
      Result.INVALID
  }

  /**
   * (Unsigned) less-than comparison.
   */
  function method evalLT(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      if lhs < rhs
        then
        Result.OK(push(pop(pop(vm)),1))
      else
        Result.OK(push(pop(pop(vm)),0))
    else
      Result.INVALID
  }

  /**
   * (Unsigned) greater-than comparison.
   */
  function method evalGT(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      if lhs > rhs
        then
        Result.OK(push(pop(pop(vm)),1))
      else
        Result.OK(push(pop(pop(vm)),0))
    else
      Result.INVALID
  }

  /**
   * Signed less-than comparison.
   */
  function method evalSLT(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := Word.asI256(peek(vm,0));
      var rhs := Word.asI256(peek(vm,1));
      if lhs < rhs
        then
        Result.OK(push(pop(pop(vm)),1))
      else
        Result.OK(push(pop(pop(vm)),0))
    else
      Result.INVALID
  }

  /**
   * Signed greater-than comparison.
   */
  function method evalSGT(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := Word.asI256(peek(vm,0));
      var rhs := Word.asI256(peek(vm,1));
      if lhs > rhs
        then
        Result.OK(push(pop(pop(vm)),1))
      else
        Result.OK(push(pop(pop(vm)),0))
    else
      Result.INVALID
  }

  /**
   * Equality comparison.
   */
  function method evalEQ(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      if lhs == rhs
        then
        Result.OK(push(pop(pop(vm)),1))
      else
        Result.OK(push(pop(pop(vm)),0))
    else
      Result.INVALID
  }

  /**
   * Simple not operator.
   */
  function method evalISZERO(vm:T) : Result {
    if operands(vm) >= 1
      then
      var mhs := peek(vm,0);
      if mhs == 0
        then
        Result.OK(push(pop(vm),1))
      else
        Result.OK(push(pop(vm),0))
    else
      Result.INVALID
  }

  /**
   * Bitwise AND operation.
   */
  function method evalAND(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as bv256;
      var rhs := peek(vm,1) as bv256;
      var res := (lhs & rhs) as u256;
      Result.OK(push(pop(pop(vm)),res))
    else
      Result.INVALID
  }

  /**
   * Bitwise OR operation.
   */
  function method {:verify false} evalOR(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as bv256;
      var rhs := peek(vm,1) as bv256;
      var res := (lhs | rhs) as u256;
      Result.OK(push(pop(pop(vm)),res))
    else
      Result.INVALID
  }

  /**
   * Bitwise XOR operation.
   */
  function method {:verify false} evalXOR(vm:T) : Result {
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as bv256;
      var rhs := peek(vm,1) as bv256;
      var res := (lhs ^ rhs) as u256;
      Result.OK(push(pop(pop(vm)),res))
    else
      Result.INVALID
  }

  /**
   * Bitwise NOT operation.
   */
  function method evalNOT(vm:T) : Result {
    if operands(vm) >= 1
      then
      var mhs := peek(vm,0) as bv256;
      var res := (!mhs) as u256;
      Result.OK(push(pop(vm),res))
    else
      Result.INVALID
  }

  /**
   * Pop word from stack.
   */
  function method evalPOP(vm:T) : Result {
    if operands(vm) >= 1
    then
      Result.OK(pop(vm))
    else
      Result.INVALID
  }

  /**
   * Get word from memory.
   */
  function method evalMLOAD(vm:T) : Result {
    if operands(vm) >= 1
      then
      var loc := peek(vm,0);
      // NOTE: This condition is not specified in the yellow paper.
      // Its not clear whether that was intended or not.  However, its
      // impossible to trigger this in practice (due to the gas costs
      // involved).
      if (loc as int) + 31 <= MAX_U256
        then
        var val := read(vm,loc);
        // Write big endian order
        Result.OK(push(pop(vm),val))
      else
        Result.INVALID
    else
      Result.INVALID
  }


  /**
   * Save word to memory.
   */
  function method evalMSTORE(vm:T) : Result {
    if operands(vm) >= 2
      then
      var loc := peek(vm,0);
      var val := peek(vm,1);
      // NOTE: This condition is not specified in the yellow paper.
      // Its not clear whether that was intended or not.  However, its
      // impossible to trigger this in practice (due to the gas costs
      // involved).
      if (loc as int) + 31 <= MAX_U256
        then
        // Write big endian order
        Result.OK(write(pop(pop(vm)),loc,val))
      else
        Result.INVALID
    else
      Result.INVALID
  }

  /**
   * Save byte to memory.
   */
  function method evalMSTORE8(vm:T) : Result {
    if operands(vm) >= 2
      then
      var loc := peek(vm,0);
      var val := (peek(vm,1) % 256) as u8;
      if (loc as int) < MAX_U256
        then
        // Write byte
        Result.OK(write8(pop(pop(vm)),loc,val))
      else
        Result.INVALID
    else
      Result.INVALID
  }

  /**
   * Get word from storage.
   */
  function method evalSLOAD(vm:T) : Result {
    if operands(vm) >= 1
      then
      var loc := peek(vm,0);
      var val := load(vm,loc);
      // Store word
      Result.OK(push(pop(vm),val))
    else
      Result.INVALID
  }

  /**
   * Save word to storage.
   */
  function method evalSSTORE(vm:T) : Result {
    if operands(vm) >= 2
      then
      var loc := peek(vm,0);
      var val := peek(vm,1);
      // Store word
      Result.OK(store(pop(pop(vm)),loc,val))
    else
      Result.INVALID
  }

  /**
   * Push one byte onto stack.
   */
  function method evalPUSH1(vm:T) : Result {
    if opcode_operands(vm) >= 1 && capacity(vm) >= 1
      then
      var k := Code.decode_u8(vm.code,vm.pc);
      Result.OK(goto(push(vm,k as u256),vm.pc+1))
    else
      Result.INVALID
  }

  /**
   * Push two bytes onto stack.
   */
  function method evalPUSH2(vm:T) : Result {
    if opcode_operands(vm) >= 2 && capacity(vm) >= 1
      then
      var k1 := Code.decode_u8(vm.code,vm.pc) as u256;
      var k2 := Code.decode_u8(vm.code,vm.pc + 1) as u256;
      var k := (k1 * 256) + k2;
      Result.OK(goto(push(vm,k),vm.pc+2))
    else
      Result.INVALID
  }

  /**
   * Duplicate item on stack.
   */
  function method evalDUP(vm:T, k: nat) : Result {
    if operands(vm) > k && capacity(vm) >= 1
      then
      var kth := peek(vm,k);
      Result.OK(push(vm,kth))
    else
      Result.INVALID
  }

  /**
   * Swap two items on the stack
   */
  function method evalSWAP(vm:T, k: nat) : Result {
    if operands(vm) > k
      then
      Result.OK(swap(vm,k))
    else
      Result.INVALID
  }

  /**
   * Halt execution returning output data.
   */
  function method evalRETURN(vm:T) : Result {
    if operands(vm) >= 2
      then
      // Determine amount of data to return.
      var len := peek(vm,1) as int;
      var start := peek(vm,0) as int;
      // Sanity check bounds
      if (start+len) <= MAX_U256
      then
        // Read out that data.
        var data := Memory.slice(vm.memory, start as u256, len);
        // Done
        Result.RETURNS(gas:=0,data:=data)
      else
        Result.INVALID
    else
      Result.INVALID
  }

  // =============================================================================
  // Microcode
  // =============================================================================

  /**
   * Decode next opcode from machine.
   */
  function method decode(vm:T) : (T,u8) {
    if vm.pc < Code.size(vm.code)
    then
      (goto(vm,vm.pc+1),Code.decode_u8(vm.code,vm.pc))
    else
      (vm,STOP)
  }

  /**
   * Move program counter to a given location.
   */
  function method goto(vm:T, k:u256) : T
    requires k <= Code.size(vm.code) {
      EVM(stack:=vm.stack,
        storage:=vm.storage,
        memory:=vm.memory,
        code:=vm.code,
        gas := vm.gas,
        pc := k
        )
  }

  /**
   * Check at least k operands on the stack.
   */
  function method operands(vm:T) : nat {
    Stack.size(vm.stack)
  }

  /**
   * Check capacity remaining on stack.
   */
  function method capacity(vm:T) : nat {
    Stack.capacity(vm.stack)
  }

  /**
   * Push word onto stack.
   */
  function method push(vm:T, v:u256) : T
    requires capacity(vm) > 0 {
        EVM(stack:=Stack.push(vm.stack,v),
          storage:=vm.storage,
          memory:=vm.memory,
          code:=vm.code,
          gas := vm.gas,
          pc:=vm.pc)
  }

  /**
   * Peek word from a given position on the stack, where "1" is the
   * topmost position, "2" is the next position and so on.
   */
  function method peek(vm:T, k:int) : u256
    // Sanity check peek possible
    requires k >= 0 && k < Stack.size(vm.stack) {
        Stack.peek(vm.stack,k)
  }

  /**
   * Pop word from stack.
   */
  function method pop(vm:T) : T
    // Cannot pop from empty stack
    requires Stack.size(vm.stack) >= 1 {
        EVM(stack:=Stack.pop(vm.stack),
          storage:=vm.storage,
          memory:=vm.memory,
          code:=vm.code,
          gas := vm.gas,
          pc:=vm.pc)
  }

  // Swap top item with kth item.
  function method swap(vm:T, k:nat) : T
  requires operands(vm) > k {
    EVM(stack:=Stack.swap(vm.stack,k),
      storage:=vm.storage,
      memory:=vm.memory,
      code:=vm.code,
      gas := vm.gas,
      pc:=vm.pc)
  }

  /**
   * Read word from byte address in memory.
   */
  function method read(vm:T, address:u256) : u256
  requires (address as int) + 31 <= MAX_U256 {
    Memory.read_u256(vm.memory,address)
  }

  /**
   * Write word to byte address in memory.
   */
  function method write(vm:T, address:u256, val: u256) : T
  requires (address as int) + 31 <= MAX_U256 {
    EVM(stack:=vm.stack,
      storage:=vm.storage,
      memory:=Memory.write_u256(vm.memory,address,val),
      code:=vm.code,
      gas := vm.gas,
      pc:=vm.pc)
  }

  /**
   * Write byte to byte address in memory.
   */
  function method write8(vm:T, address:u256, val: u8) : T
  requires (address as int) < MAX_U256 {
    EVM(stack:=vm.stack,
      storage:=vm.storage,
      memory:=Memory.write_u8(vm.memory,address,val),
      code:=vm.code,
      gas := vm.gas,
      pc:=vm.pc)
  }

  /**
   * Read word from storage
   */
  function method load(vm:T, address:u256) : u256 {
    Storage.read(vm.storage,address)
  }

  /**
   * Write word to storage
   */
  function method store(vm:T, address:u256, val: u256) : T {
    EVM(stack:=vm.stack,
      storage:=Storage.write(vm.storage,address,val),
      memory:=vm.memory,
      code:=vm.code,
      gas := vm.gas,
      pc:=vm.pc)
  }

  /**
   * Check how many code operands are available.
   */
  function method opcode_operands(vm:T) : int {
    (Code.size(vm.code) as nat) - (vm.pc as nat)
  }


  /**
   * Unsigned integer division with handling for zero.
   */
  function method div(lhs:u256, rhs:u256) : u256 {
    if rhs == 0 then 0 as u256
    else
      (lhs / rhs) as u256
  }

  /**
   * Unsigned integer remainder with handling for zero.
   */
  function method mod(lhs:u256, rhs:u256) : u256 {
    if rhs == 0 then 0 as u256
    else
      (lhs % rhs) as u256
  }

  /**
   * Signed integer division with handling for zero and overflow.
   * A key challenge here is that, in Dafny, division is Euclidean
   * (i.e. rounds down).  In contrast, division on the EVM is
   * non-Euclidean (i.e. rounds towards zero).  This means we cannot
   * use Dafny's division operator as is for implementing SDIV
   * (though for DIV it is OK).  Instead, we have to explicitly
   * manage the cases for negative operands.
   */
  function method sdiv(lhs:i256, rhs:i256) : i256 {
    if rhs == 0 then 0 as i256
    else if rhs == -1 && lhs == (-TWO_255 as i256)
    then
      -TWO_255 as i256
    else
      // Do not use Dafny's division operator here!
      I256.div(lhs,rhs)
  }

  /**
   * Signed integer remainder with handling for zero.
   * A key challenge here is that, in Dafny, division is Euclidean
   * (i.e. rounds down).  In contrast, division on the EVM is
   * non-Euclidean (i.e. rounds towards zero).  This means we cannot
   * use Dafny's remainder operator as is for implementing SMOD
   * (though for MOD it is OK).  Instead, we have to explicitly
   * manage the cases for negative operands.
   */
  function method smod(lhs:i256, rhs:i256) : i256 {
    if rhs == 0 then 0 as i256
    else
      // Do not use Dafny's remainder operator here!
      I256.rem(lhs,rhs)
  }
}
