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
include "util/context.dfy"
include "util/code.dfy"

include "./evm-opcodes.dfy"
include "./evm-types.dfy"

/**
 * Top-level definition of an Ethereum Virtual Machine.
 */
module EVM {
  import opened Int
  import U256
  import I256
  import Word
  import Stack
  import Memory
  import Storage
  import Context
  import Code

  import opened EVM_TYPES
  import opened EVM_OPCODES 

  // datatype T = EVM(
  //   context: Context.T,
  //   storage : Storage.T,
  //   stack   : Stack.T,
  //   memory  : Memory.T,
  //   code: Code.T,
  //   gas: nat,
  //   pc : u256
  // )

  /**
   * Create a fresh EVM to execute a given sequence of bytecode instructions.
   * The EVM is initialised with an empty stack and empty local memory.
   */
  function method create(context: Context.T, storage: map<u256,u256>, gas: nat, code: seq<u8>) : State
  requires |code| <= MAX_U256 {
    var stck := Stack.create();
    var mem := Memory.create();
    var sto := Storage.create(storage);
    var cod := Code.create(code);
    var evm := EVM(stack:=stck,memory:=mem,storage:=sto,context:=context,code:=cod,gas:=gas,pc:=0);
    // Off we go!
    State.OK(evm)
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
	const SHL : u8 := 0x1b;
  const SHR : u8 := 0x1c;
  const SAR : u8 := 0x1d;
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
   * Captures the possible state of the machine.  Normal execution is indicated
   * by OK (with the current machine data).  An exceptional halt is indicated by INVALID
   * (e.g. insufficient gas, insufficient stack operands, etc).  Finally, a RETURN or REVERT
   * with return data are indicated accordingly (along with any gas returned).
   */
  // datatype State = OK(evm:T) | INVALID | RETURNS(gas:nat,data:seq<u8>) | REVERT(gas:nat,data:seq<u8>)

  /**
   * Execute a single step of the EVM.  This either States in a valid EVM (i.e. so execution
   * can continue), or some form of halt (e.g. exceptional, revert, etc).
   */
  function method execute(st:State) : State
  // To execute a bytecode requires the machine is in a non-terminal state.
  requires st.OK? {
    var OK(vm) := st;
    // Decode
    var opcode := decode(st);
    // 0x00s: STOP & Arithmetic
    if opcode == STOP then Stop(st)
    else if opcode == ADD then Add(st)
    else if opcode == MUL then Mul(st)
    else if opcode == SUB then Sub(st)
    else if opcode == DIV then Div(st)
    else if opcode == SDIV then SDiv(st)
    else if opcode == MOD then Mod(st)
    else if opcode == SMOD then SMod(st)
    else if opcode == ADDMOD then AddMod(st)
    else if opcode == MULMOD then MulMod(st)
    // else if opcode == EXP then evalEXP(st)
    // else if opcode == SIGNEXTEND then evalSIGNEXTEND(st)
    // 0x10s: Comparison & Bitwise Logic
    else if opcode == LT then Lt(st)
    else if opcode == GT then Gt(st)
    else if opcode == SLT then SLt(st)
    else if opcode == SGT then SGt(st)
    else if opcode == EQ then Eq(st)
    else if opcode == ISZERO then IsZero(st)
    else if opcode == AND then And(st)
    else if opcode == OR then Or(st)
    else if opcode == XOR then Xor(st)
    else if opcode == NOT then Not(st)
    else if opcode == BYTE then Byte(st)
    else if opcode == SHL then Shl(st)
    else if opcode == SHR then Shr(st)
    // else if opcode == SAR then evalSAR(st)
    // 0x20s
    // else if opcode == KECCAK256 then evalKECCAK256(st)
    // 0x30s: Environment Information
    // else if opcode == ADDRESS then evalADDRESS(st)
    // else if opcode == BALANCE then evalBALANCE(st)
    // else if opcode == ORIGIN then evalORIGIN(st)
    // else if opcode == CALLER then evalCALLER(st)
    // else if opcode == CALLVALUE then evalCALLVALUE(st)
    else if opcode == CALLDATALOAD then CallDataLoad(st)
    else if opcode == CALLDATASIZE then CallDataSize(st)
    else if opcode == CALLDATACOPY then CallDataCopy(st)
    // else if opcode == CODESIZE then evalCODESIZE(st)
    // else if opcode == CODECOPY then evalCODECOPY(st)
    // else if opcode == GASPRICE then evalGASPRICE(st)
    // else if opcode == EXTCODESIZE then evalEXTCODESIZE(st)
    // else if opcode == EXTCODECOPY then evalEXTCODECOPY(st)
    // else if opcode == RETURNDATASIZE then evalRETURNDATASIZE(st)
    // else if opcode == RETURNDATACOPY then evalRETURNDATACOPY(st)
    // else if opcode == EXTCODEHASH then evalEXTCODEHASH(st)
    // 0x40s: Block Information
    // else if opcode == BLOCKHASH then evalBLOCKHASH(st)
    // else if opcode == COINBASE then evalCOINBASE(st)
    // else if opcode == TIMESTAMP then evalTIMESTAMP(st)
    // else if opcode == NUMBER then evalNUMBER(st)
    // else if opcode == DIFFICULTY then evalDIFFICULTY(st)
    // else if opcode == GASLIMIT then evalGASLIMIT(st)
    // else if opcode == CHAINID then evalCHAINID(st)
    // else if opcode == SELFBALANCE then evalSELFBALANCE(st)
    // 0x50s: Stack, Memory, Storage and Flow
    else if opcode == POP then Pop(st)
    else if opcode == MLOAD then MLoad(st)
    else if opcode == MSTORE then MStore(st)
    else if opcode == MSTORE8 then MStore8(st)
    else if opcode == SLOAD then SLoad(st)
    else if opcode == SSTORE then SStore(st)
    else if opcode == JUMP then Jump(st)
    else if opcode == JUMPI then JumpI(st)
    else if opcode == PC then Pc(st)
    else if opcode == JUMPDEST then JumpDest(st)
    // 0x60s & 0x70s: Push operations
    else if opcode == PUSH1 && opcode_operands(vm) >= 1 then
      var k := Code.decode_u8(vm.code, (vm.pc + 1) as nat);
      Push1(st, k)
    else if opcode == PUSH2 && opcode_operands(vm) >= 2 then
      var k := Code.decode_u16(vm.code, (vm.pc + 1) as nat);
      Push2(st, k)
    // 0x80s: Duplicate operations
    else if DUP1 <= opcode <= DUP16 then
      var k := (opcode - DUP1) as int; Dup(st,k)
    // 0x90s: Exchange operations
    else if SWAP1 <= opcode <= SWAP16 then
      var k := (opcode - SWAP1) as int; Swap(st,k+1)
    // 0xA0s: Log operations
    // else if LOG0 <= opcode <= LOG4 then
    //   var k := (opcode - LOG0) as int; evalLOG(st,k)
    // 0xf0
    // else if opcode == CREATE then evalCREATE(st)
    // else if opcode == CALL then evalCALL(st)
    // else if opcode == CALLCODE then evalCALLCODE(st)
    else if opcode == RETURN then Return(st)
    //else if opcode == DELEGATECALL then evalDELEGATECALL(st)
    //else if opcode == CREATE2 then evalCREATE2(st)
    //else if opcode == STATICCALL then evalSTATICCALL(st)
    else if opcode == REVERT then Revert(st)
    //else if opcode == SELFDESTRUCT then evalSELFDESTRUCT(st)
    else
      // Invalid opcode
      State.INVALID
  }

  /**
   * Evaluate the STOP bytecode.  This halts the machine without
   * return output data.
   */
  function method Stop(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    State.RETURNS(gas:=vm.gas,data:=[])
  }

  /**
   * Unsigned integer addition with modulo arithmetic.
   */
  function method Add(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var res := (lhs + rhs) % TWO_256;
      next(push(pop(pop(vm)),res as u256))
    else
      State.INVALID
  }

  /**
   * Unsigned integer multiplication with modulo arithmetic.
   */
  function method Mul(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var res := (lhs * rhs) % TWO_256;
      next(push(pop(pop(vm)),res as u256))
    else
      State.INVALID
  }

  /**
   * Unsigned integer subtraction with modulo arithmetic.
   */
  function method Sub(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var res := (lhs - rhs) % TWO_256;
      next(push(pop(pop(vm)),res as u256))
    else
      State.INVALID
  }

  /**
   * Unsigned integer division.
   */
  function method Div(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      var res := div(lhs,rhs) as u256;
      next(push(pop(pop(vm)),res))
    else
      State.INVALID
  }

  /**
   * Signed integer division.
   */
  function method SDiv(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := Word.asI256(peek(vm,0));
      var rhs := Word.asI256(peek(vm,1));
      var res := Word.fromI256(sdiv(lhs,rhs));
      next(push(pop(pop(vm)),res))
    else
      State.INVALID
  }

  /**
   * (Unsigned) Modulo remainder.
   */
  function method Mod(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      var res := mod(lhs,rhs) as u256;
      next(push(pop(pop(vm)),res))
    else
      State.INVALID
  }

  /**
   * Signed integer remainder:
   */
  function method SMod(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := Word.asI256(peek(vm,0));
      var rhs := Word.asI256(peek(vm,1));
      var res := Word.fromI256(smod(lhs,rhs));
      next(push(pop(pop(vm)),res))
    else
      State.INVALID
  }

  /**
   * Unsigned integer modulo addition.
   */
  function method AddMod(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 3
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var rem := peek(vm,2) as int;
      var res := if rem == 0 then 0 else(lhs + rhs) % rem;
      next(push(pop(pop(pop(vm))),res as u256))
    else
      State.INVALID
  }

  /**
   * Unsigned integer modulo multiplication.
   */
  function method MulMod(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 3
      then
      var lhs := peek(vm,0) as int;
      var rhs := peek(vm,1) as int;
      var rem := peek(vm,2) as int;
      var res := if rem == 0 then 0 else(lhs * rhs) % rem;
      next(push(pop(pop(pop(vm))),res as u256))
    else
      State.INVALID
  }

  /**
   * (Unsigned) less-than comparison.
   */
  function method Lt(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      if lhs < rhs
        then
        next(push(pop(pop(vm)),1))
      else
        next(push(pop(pop(vm)),0))
    else
      State.INVALID
  }

  /**
   * (Unsigned) greater-than comparison.
   */
  function method Gt(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      if lhs > rhs
        then
        next(push(pop(pop(vm)),1))
      else
        next(push(pop(pop(vm)),0))
    else
      State.INVALID
  }

  /**
   * Signed less-than comparison.
   */
  function method SLt(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := Word.asI256(peek(vm,0));
      var rhs := Word.asI256(peek(vm,1));
      if lhs < rhs
        then
        next(push(pop(pop(vm)),1))
      else
        next(push(pop(pop(vm)),0))
    else
      State.INVALID
  }

  /**
   * Signed greater-than comparison.
   */
  function method SGt(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := Word.asI256(peek(vm,0));
      var rhs := Word.asI256(peek(vm,1));
      if lhs > rhs
        then
        next(push(pop(pop(vm)),1))
      else
        next(push(pop(pop(vm)),0))
    else
      State.INVALID
  }

  /**
   * Equality comparison.
   */
  function method Eq(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1);
      if lhs == rhs
        then
        next(push(pop(pop(vm)),1))
      else
        next(push(pop(pop(vm)),0))
    else
      State.INVALID
  }

  /**
   * Simple not operator.
   */
  function method IsZero(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 1
      then
      var mhs := peek(vm,0);
      if mhs == 0
        then
        next(push(pop(vm),1))
      else
        next(push(pop(vm),0))
    else
      State.INVALID
  }

  /**
   * Bitwise AND operation.
   */
  function method And(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as bv256;
      var rhs := peek(vm,1) as bv256;
      var res := (lhs & rhs) as u256;
      next(push(pop(pop(vm)),res))
    else
      State.INVALID
  }

  /**
   * Bitwise OR operation.
   */
  function method {:verify false} Or(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as bv256;
      var rhs := peek(vm,1) as bv256;
      var res := (lhs | rhs) as u256;
      next(push(pop(pop(vm)),res))
    else
      State.INVALID
  }

  /**
   * Bitwise XOR operation.
   */
  function method {:verify false} Xor(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0) as bv256;
      var rhs := peek(vm,1) as bv256;
      var res := (lhs ^ rhs) as u256;
      next(push(pop(pop(vm)),res))
    else
      State.INVALID
  }

  /**
   * Bitwise NOT operation.
   */
  function method Not(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 1
      then
      var mhs := peek(vm,0) as bv256;
      var res := (!mhs) as u256;
      next(push(pop(vm),res))
    else
      State.INVALID
  }

  /**
   * Retrieve single byte from word.
   */
  function method Byte(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var val := peek(vm,1);
      var k := peek(vm,0);
      var res := if k < 32 then U256.nth_u8(val,k as int) else 0;
      next(push(pop(pop(vm)),res as u256))
    else
      State.INVALID
  }

  /**
   * Left shift operation.
   */
  function method Shl(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1) as bv256;
      // NOTE: unclear whether shifting is optimal choice here.
      var res := if lhs < 256 then (rhs << lhs) else 0;
      next(push(pop(pop(vm)),res as u256))
    else
      State.INVALID
  }

  /**
   * Right shift operation.
   */
  function method {:verify false} Shr(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var lhs := peek(vm,0);
      var rhs := peek(vm,1) as bv256;
      // NOTE: unclear whether shifting is optimal choice here.
      var res := if lhs < 256 then (rhs >> lhs) else 0;
      next(push(pop(pop(vm)),res as u256))
    else
      State.INVALID
  }

  /**
   * Get input data from the current environment.
   */
  function method CallDataLoad(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 1
      then
      var loc := peek(vm,0);
      var val := if loc >= Context.data_size(vm.context) then 0
        else Context.data_read(vm.context,loc);
      next(push(pop(vm),val))
    else
      State.INVALID
  }

  /**
   * Get size of input data in current environment.
   */
  function method CallDataSize(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if capacity(vm) >= 1
      then
      var len := |vm.context.calldata|;
      next(push(vm,len as u256))
    else
      State.INVALID
  }

  /**
   * Get size of input data in current environment.
   */
  function method CallDataCopy(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 3
      then
      var m_loc := peek(vm,0);
      var d_loc := peek(vm,1);
      var len := peek(vm,2);
      // NOTE: This condition is not specified in the yellow paper.
      // Its not clear whether that was intended or not.  However, its
      // impossible to trigger this in practice (due to the gas costs
      // involved).
      if (m_loc as int) + (len as int) < MAX_U256
      then
        // Slice bytes out of call data (with padding as needed)
        var data := Context.data_slice(vm.context,d_loc,len);
        // Sanity check
        assert |data| == (len as int);
        // Copy slice into memory
        next(copy(pop(pop(pop(vm))),m_loc,data))
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Pop word from stack.
   */
  function method Pop(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 1
    then
      next(pop(vm))
    else
      State.INVALID
  }

  /**
   * Get word from memory.
   */
  function method MLoad(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
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
        next(push(pop(vm),val))
      else
        State.INVALID
    else
      State.INVALID
  }


  /**
   * Save word to memory.
   */
  function method MStore(st: State) : State
  requires st.OK? {

    var OK(vm) := st;
    //
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
        next(write(pop(pop(vm)),loc,val))
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Save byte to memory.
   */
  function method MStore8(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var loc := peek(vm,0);
      var val := (peek(vm,1) % 256) as u8;
      if (loc as int) < MAX_U256
        then
        // Write byte
        next(write8(pop(pop(vm)),loc,val))
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Get word from storage.
   */
  function method SLoad(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 1
      then
      var loc := peek(vm,0);
      var val := load(vm,loc);
      // Store word
      next(push(pop(vm),val))
    else
      State.INVALID
  }

  /**
   * Save word to storage.
   */
  function method SStore(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var loc := peek(vm,0);
      var val := peek(vm,1);
      // Store word
      next(store(pop(pop(vm)),loc,val))
    else
      State.INVALID
  }

  /**
   * Unconditional branch.
   */
  function method Jump(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 1
      then
      var pc := peek(vm,0);
      // Check valid branch target
      if pc < Code.size(vm.code) && Code.decode_u8(vm.code,pc as nat) == JUMPDEST
      then
        goto(pop(vm),pc)
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Unconditional branch.
   */
  function method JumpI(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) >= 2
      then
      var pc := peek(vm,0);
      var val := peek(vm,1);
      // Check branch taken or not
      if val == 0 then next(pop(pop(vm)))
      // Check valid branch target
      else if pc < Code.size(vm.code) && Code.decode_u8(vm.code,pc as nat) == JUMPDEST
      then
        goto(pop(pop(vm)),pc)
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Gets value of program counter prior to this instruction being executed.
   */
  function method Pc(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if capacity(vm) >= 1
    then
      next(push(vm, vm.pc))
    else
      State.INVALID
  }

  /**
   * Marks a valid destination for a jump, but otherwise has no effect
   * on machine state.
   */
  function method JumpDest(st: State) : State
  requires st.OK? {
    var OK(vm) := st; next(vm)
  }

  /**
   * Push one byte onto stack.
   */
  function method Push1(st: State, k: u8) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if capacity(vm) >= 1
      then
      skip(push(vm,k as u256),2)
    else
      State.INVALID
  }

  /**
   * Push two bytes onto stack.
   */
  function method Push2(st: State, k: u16) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if capacity(vm) >= 1
      then
      skip(push(vm,k as u256),3)
    else
      State.INVALID
  }

  /**
   * Duplicate item on stack.
   */
  function method Dup(st: State, k: nat) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) > k && capacity(vm) >= 1
      then
      var kth := peek(vm,k);
      next(push(vm,kth))
    else
      State.INVALID
  }

  /**
   * Swap two items on the stack
   */
  function method Swap(st: State, k: nat) : State
  requires st.OK? {
    var OK(vm) := st;
    //
    if operands(vm) > k
      then
      next(swap(vm,k))
    else
      State.INVALID
  }

  /**
   * Halt execution returning output data.
   */
  function method Return(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
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
        State.RETURNS(gas:=vm.gas,data:=data)
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Revert execution returning output data.
   */
  function method Revert(st: State) : State
  requires st.OK? {
    var OK(vm) := st;
    //
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
        State.REVERT(gas:=vm.gas,data:=data)
      else
        State.INVALID
    else
      State.INVALID
  }

  // =============================================================================
  // Microcode
  // =============================================================================

  /**
   * Decode next opcode from machine.
   */
  function method decode(st:State) : u8
   // To execute a bytecode requires the machine is in a non-terminal state.
  requires st.OK? {
    // Destructure incoming state.
    var OK(vm) := st;
    // Sanity check pc location
    if vm.pc < Code.size(vm.code)
    then
      Code.decode_u8(vm.code,vm.pc as nat)
    else
      INVALID
  }

  /**
   * Move program counter to a given location.
   */
  function method goto(evm:T, k:u256) : State {
    // Sanity check valid target address
    if k <= Code.size(evm.code)
    then State.OK(evm.(pc := k))
    else State.INVALID
  }

 /**
   * Move program counter to next instruction.
   */
  function method next(evm:T) : State {
    if evm.pc < Code.size(evm.code)
    then State.OK(evm.(pc := evm.pc + 1))
    else State.INVALID
  }

  /**
   * Move program counter over k instructions / operands.
   */
  function method skip(evm:T, k:nat) : State {
    var pc_k := (evm.pc as nat) + k;
    if pc_k < |evm.code.contents|
    then State.OK(evm.(pc := pc_k as u256))
    else State.INVALID
  }

  /**
   * Check at least k operands on the stack.
   */
  function method operands(evm:T) : nat {
    Stack.size(evm.stack)
  }

  /**
   * Check capacity remaining on stack.
   */
  function method capacity(evm:T) : nat {
    Stack.capacity(evm.stack)
  }

  /**
   * Push word onto stack.
   */
  function method push(evm:T, v:u256) : T
    requires capacity(evm) > 0 {
      evm.(stack:=Stack.push(evm.stack,v))
  }

  /**
   * Peek word from a given position on the stack, where "1" is the
   * topmost position, "2" is the next position and so on.
   */
  function method peek(evm:T, k:int) : u256
    // Sanity check peek possible
    requires k >= 0 && k < Stack.size(evm.stack) {
        Stack.peek(evm.stack,k)
  }

  /**
   * Pop word from stack.
   */
  function method pop(evm:T) : T
    // Cannot pop from empty stack
    requires Stack.size(evm.stack) >= 1 {
        evm.(stack:=Stack.pop(evm.stack))
  }

  /**
   * Swap top item with kth item.
   */
  function method swap(evm:T, k:nat) : T
    requires operands(evm) > k {
      evm.(stack:=Stack.swap(evm.stack,k))
  }

  /**
   * Read word from byte address in memory.
   */
  function method read(evm:T, address:u256) : u256
  requires (address as int) + 31 <= MAX_U256 {
    Memory.read_u256(evm.memory,address)
  }

  /**
   * Write word to byte address in memory.
   */
  function method write(evm:T, address:u256, val: u256) : T
    requires (address as int) + 31 <= MAX_U256 {
      evm.(memory:=Memory.write_u256(evm.memory,address,val))
  }

  /**
   * Write byte to byte address in memory.
   */
  function method write8(evm:T, address:u256, val: u8) : T
  requires (address as int) < MAX_U256 {
    evm.(memory := Memory.write_u8(evm.memory,address,val))
  }

  /**
   * Copy byte sequence to byte address in memory.  Any bytes
   * that overflow are dropped.
   */
  function method copy(evm:T, address:u256, data: seq<u8>) : T
    requires (address as int) + |data| <= MAX_U256 {
      evm.(memory:=Memory.copy(evm.memory,address,data))
  }

  /**
   * Read word from storage
   */
  function method load(evm:T, address:u256) : u256 {
    Storage.read(evm.storage,address)
  }

  /**
   * Write word to storage
   */
  function method store(evm:T, address:u256, val: u256) : T {
    evm.(storage:=Storage.write(evm.storage,address,val))
  }

  /**
   * Check how many code operands are available.
   */
  function method opcode_operands(evm:T) : int {
    (Code.size(evm.code) as nat) - ((evm.pc as nat) + 1)
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
