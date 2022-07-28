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

  datatype T = EVM(
    context: Context.T,
    storage : Storage.T,
    stack   : Stack.T,
    memory  : Memory.T,
    code: Code.T,
    gas: nat,
    pc : u256
  )

  /**
   * Create a fresh EVM to execute a given sequence of bytecode instructions.
   * The EVM is initialised with an empty stack and empty local memory.
   */
  function method Create(context: Context.T, storage: map<u256,u256>, gas: nat, code: seq<u8>) : State
  requires |code| <= MAX_U256 {
    var stck := Stack.Create();
    var mem := Memory.Create();
    var sto := Storage.Create(storage);
    var cod := Code.Create(code);
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
  const INVALID_OPCODE : u8 := 0xfe; // FIXME: this duplicate of INVALID should be removed.
	const SELFDESTRUCT : u8 := 0xff;

  /**
   * Captures the possible state of the machine.  Normal execution is indicated
   * by OK (with the current machine data).  An exceptional halt is indicated by INVALID
   * (e.g. insufficient gas, insufficient stack operands, etc).  Finally, a RETURN or REVERT
   * with return data are indicated accordingly (along with any gas returned).
   */
  datatype State = OK(evm:T)
    | INVALID
    | RETURNS(gas:nat,data:seq<u8>)
    | REVERTS(gas:nat,data:seq<u8>) {

    /**
     * Check whether EVM has failed (e.g. due to an exception
     * or a revert, etc) or not.
     */
    predicate method IsFailure() {
			!this.OK?
		}
    /**
     * Extract underlying raw state.
     */
		function method Unwrap(): T
			requires !IsFailure() {
			this.evm
		}
    /**
     * Determine number of operands on stack.
     */
    function method Operands() : nat
    requires !IsFailure() {
      Stack.Size(evm.stack)
    }
    /**
     * Determine remaining gas.
     */
    function method Gas(): nat
				requires !IsFailure() {
			this.evm.gas
		}
    /**
     * Determine current PC value.
     */
		function method PC(): u256
			requires !IsFailure() {
			this.evm.pc
		}
    /**
     * Get the state of the internal stack.
     */
		function method GetStack(): Stack.T
		requires !IsFailure() {
			this.evm.stack
		}

    /**
     * Read word from byte address in memory.
     */
    function method Read(address:u256) : u256
    requires !IsFailure()
    requires (address as int) + 31 <= MAX_U256 {
      Memory.ReadUint256(evm.memory,address)
    }

    /**
     * Write word to byte address in memory.
     */
    function method Write(address:u256, val: u256) : State
    requires !IsFailure()
    requires (address as int) + 31 <= MAX_U256 {
      OK(evm.(memory:=Memory.WriteUint256(evm.memory,address,val)))
    }

    /**
     * Write byte to byte address in memory.
     */
    function method Write8(address:u256, val: u8) : State
    requires (address as int) < MAX_U256
    requires !IsFailure() {
      OK(evm.(memory := Memory.WriteUint8(evm.memory,address,val)))
    }

    /**
     * Copy byte sequence to byte address in memory.  Any bytes
     * that overflow are dropped.
     */
    function method Copy(address:u256, data: seq<u8>) : State
    requires (address as int) + |data| <= MAX_U256
    requires !IsFailure() {
      OK(evm.(memory:=Memory.Copy(evm.memory,address,data)))
    }

    /**
     * Write word to storage
     */
    function method Store(address:u256, val: u256) : State
    requires !IsFailure() {
      OK(evm.(storage:=Storage.Write(evm.storage,address,val)))
    }

    /**
     * Read word from storage
     */
    function method Load(address:u256) : u256
			requires !IsFailure() {
      Storage.Read(evm.storage,address)
    }

    /**
     * Decode next opcode from machine.
     */
    function method Decode() : u8
		requires !IsFailure() {
      // Sanity check pc location
      if evm.pc < Code.Size(evm.code)
      then
        Code.DecodeUint8(evm.code,evm.pc as nat)
      else
        INVALID_OPCODE
    }

    /**
     * Move program counter to a given location.
     */
    function method Goto(k:u256) : State
    requires !IsFailure() {
      // Sanity check valid target address
      if k <= Code.Size(evm.code)
      then State.OK(evm.(pc := k))
      else State.INVALID
    }

    /**
     * Move program counter to next instruction.
     */
    function method Next() : State
    requires !IsFailure() {
      if evm.pc < Code.Size(evm.code)
     then State.OK(evm.(pc := evm.pc + 1))
     else State.INVALID
    }

    /**
     * Move program counter over k instructions / operands.
     */
    function method Skip(k:nat) : State
    requires !IsFailure() {
      var pc_k := (evm.pc as nat) + k;
      if pc_k < |evm.code.contents|
      then State.OK(evm.(pc := pc_k as u256))
      else State.INVALID
    }

    /**
     * Check capacity remaining on stack.
     */
    function method Capacity() : nat
    requires !IsFailure() {
      Stack.Capacity(evm.stack)
    }

    /**
     * Push word onto stack.
     */
    function method Push(v:u256) : State
    requires !IsFailure()
    requires Capacity() > 0 {
      OK(evm.(stack:=Stack.Push(evm.stack,v)))
    }

    /**
     * peek word from a given position on the stack, where "1" is the
     * topmost position, "2" is the next position and so on.
     */
    function method Peek(k:nat) : u256
    requires !IsFailure()
    // Sanity check peek possible
    requires k < Stack.Size(evm.stack) {
        Stack.Peek(evm.stack,k)
    }

    /**
     * Pop word from stack.
     */
    function method Pop() : State
    requires !IsFailure()
    // Cannot pop from empty stack
    requires Stack.Size(evm.stack) >= 1 {
        OK(evm.(stack:=Stack.Pop(evm.stack)))
    }

    /**
     * Swap top item with kth item.
     */
    function method Swap(k:nat) : State
    requires !IsFailure()
    requires Operands() > k {
      OK(evm.(stack:=Stack.Swap(evm.stack,k)))
    }

    /**
     * Check how many code operands are available.
     */
    function method CodeOperands() : int
    requires !IsFailure() {
      (Code.Size(evm.code) as nat) - ((evm.pc as nat) + 1)
    }

    /**
     * Check whether a given Program Counter location holds the JUMPDEST bytecode.
     */
    predicate method IsJumpDest(pc: u256)
    requires !IsFailure() {
      pc < Code.Size(evm.code) && Code.DecodeUint8(evm.code,pc as nat) == JUMPDEST
    }
  }

  /**
   * Execute a single step of the EVM.  This either States in a valid EVM (i.e. so execution
   * can continue), or some form of halt (e.g. exceptional, revert, etc).
   */
  function method Execute(st:State) : State
  // To execute a bytecode requires the machine is in a non-terminal state.
  requires !st.IsFailure() {
    var OK(vm) := st;
    // Decode
    var opcode := st.Decode();
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
    else if opcode == PUSH1 && st.CodeOperands() >= 1 then
      var k := Code.DecodeUint8(vm.code, (vm.pc + 1) as nat);
      Push1(st, k)
    else if opcode == PUSH2 && st.CodeOperands() >= 2 then
      var k := Code.DecodeUint16(vm.code, (vm.pc + 1) as nat);
      Push2(st, k)
    // 0x80s: Duplicate operations
    else if DUP1 <= opcode <= DUP16 then
      var k := (opcode - DUP1) as int; Dup(st,k+1)
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
  requires !st.IsFailure() {
    var OK(vm) := st;
    //
    State.RETURNS(gas:=vm.gas,data:=[])
  }

  /**
   * Unsigned integer addition with modulo arithmetic.
   */
  function method Add(st: State) : State
  requires !st.IsFailure() {
    var OK(vm) := st;
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0) as int;
      var rhs := st.Peek(1) as int;
      var res := (lhs + rhs) % TWO_256;
      st.Pop().Pop().Push(res as u256).Next()
    else
      State.INVALID
  }

  /**
   * Unsigned integer multiplication with modulo arithmetic.
   */
  function method Mul(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0) as int;
      var rhs := st.Peek(1) as int;
      var res := (lhs * rhs) % TWO_256;
      st.Pop().Pop().Push(res as u256).Next()
    else
      State.INVALID
  }

  /**
   * Unsigned integer subtraction with modulo arithmetic.
   */
  function method Sub(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0) as int;
      var rhs := st.Peek(1) as int;
      var res := (lhs - rhs) % TWO_256;
      st.Pop().Pop().Push(res as u256).Next()
    else
      State.INVALID
  }

  /**
   * Unsigned integer division.
   */
  function method Div(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0);
      var rhs := st.Peek(1);
      var res := DivWithZero(lhs,rhs) as u256;
      st.Pop().Pop().Push(res).Next()
    else
      State.INVALID
  }

  /**
   * Signed integer division.
   */
  function method SDiv(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := Word.asI256(st.Peek(0));
      var rhs := Word.asI256(st.Peek(1));
      var res := Word.fromI256(SDivWithZero(lhs,rhs));
      st.Pop().Pop().Push(res).Next()
    else
      State.INVALID
  }

  /**
   * (Unsigned) Modulo remainder.
   */
  function method Mod(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0);
      var rhs := st.Peek(1);
      var res := ModWithZero(lhs,rhs) as u256;
      st.Pop().Pop().Push(res).Next()
    else
      State.INVALID
  }

  /**
   * Signed integer remainder:
   */
  function method SMod(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := Word.asI256(st.Peek(0));
      var rhs := Word.asI256(st.Peek(1));
      var res := Word.fromI256(SModWithZero(lhs,rhs));
      st.Pop().Pop().Push(res).Next()
    else
      State.INVALID
  }

  /**
   * Unsigned integer modulo addition.
   */
  function method AddMod(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 3
      then
      var lhs := st.Peek(0) as int;
      var rhs := st.Peek(1) as int;
      var rem := st.Peek(2) as int;
      var res := if rem == 0 then 0 else(lhs + rhs) % rem;
      st.Pop().Pop().Pop().Push(res as u256).Next()
    else
      State.INVALID
  }

  /**
   * Unsigned integer modulo multiplication.
   */
  function method MulMod(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 3
      then
      var lhs := st.Peek(0) as int;
      var rhs := st.Peek(1) as int;
      var rem := st.Peek(2) as int;
      var res := if rem == 0 then 0 else(lhs * rhs) % rem;
      st.Pop().Pop().Pop().Push(res as u256).Next()
    else
      State.INVALID
  }

  /**
   * (Unsigned) less-than comparison.
   */
  function method Lt(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0);
      var rhs := st.Peek(1);
      if lhs < rhs
        then
        st.Pop().Pop().Push(1).Next()
      else
        st.Pop().Pop().Push(0).Next()
    else
      State.INVALID
  }

  /**
   * (Unsigned) greater-than comparison.
   */
  function method Gt(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0);
      var rhs := st.Peek(1);
      if lhs > rhs
        then
        st.Pop().Pop().Push(1).Next()
      else
        st.Pop().Pop().Push(0).Next()
    else
      State.INVALID
  }

  /**
   * Signed less-than comparison.
   */
  function method SLt(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := Word.asI256(st.Peek(0));
      var rhs := Word.asI256(st.Peek(1));
      if lhs < rhs
        then
        st.Pop().Pop().Push(1).Next()
      else
        st.Pop().Pop().Push(0).Next()
    else
      State.INVALID
  }

  /**
   * Signed greater-than comparison.
   */
  function method SGt(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := Word.asI256(st.Peek(0));
      var rhs := Word.asI256(st.Peek(1));
      if lhs > rhs
        then
        st.Pop().Pop().Push(1).Next()
      else
        st.Pop().Pop().Push(0).Next()
    else
      State.INVALID
  }

  /**
   * Equality comparison.
   */
  function method Eq(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0);
      var rhs := st.Peek(1);
      if lhs == rhs
        then
        st.Pop().Pop().Push(1).Next()
      else
        st.Pop().Pop().Push(0).Next()
    else
      State.INVALID
  }

  /**
   * Simple not operator.
   */
  function method IsZero(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 1
      then
      var mhs := st.Peek(0);
      if mhs == 0
        then
        st.Pop().Push(1).Next()
      else
        st.Pop().Push(0).Next()
    else
      State.INVALID
  }

  /**
   * Bitwise AND operation.
   */
  function method And(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0) as bv256;
      var rhs := st.Peek(1) as bv256;
      var res := (lhs & rhs) as u256;
      st.Pop().Pop().Push(res).Next()
    else
      State.INVALID
  }

  /**
   * Bitwise OR operation.
   */
  function method {:verify false} Or(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0) as bv256;
      var rhs := st.Peek(1) as bv256;
      var res := (lhs | rhs) as u256;
      st.Pop().Pop().Push(res).Next()
    else
      State.INVALID
  }

  /**
   * Bitwise XOR operation.
   */
  function method {:verify false} Xor(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0) as bv256;
      var rhs := st.Peek(1) as bv256;
      var res := (lhs ^ rhs) as u256;
      st.Pop().Pop().Push(res).Next()
    else
      State.INVALID
  }

  /**
   * Bitwise NOT operation.
   */
  function method Not(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 1
      then
      var mhs := st.Peek(0) as bv256;
      var res := (!mhs) as u256;
      st.Pop().Push(res).Next()
    else
      State.INVALID
  }

  /**
   * Retrieve single byte from word.
   */
  function method Byte(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var val := st.Peek(1);
      var k := st.Peek(0);
      var res := if k < 32 then U256.NthUint8(val,k as int) else 0;
      st.Pop().Pop().Push(res as u256).Next()
    else
      State.INVALID
  }

  /**
   * Left shift operation.
   */
  function method Shl(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0);
      var rhs := st.Peek(1) as bv256;
      // NOTE: unclear whether shifting is optimal choice here.
      var res := if lhs < 256 then (rhs << lhs) else 0;
      st.Pop().Pop().Push(res as u256).Next()
    else
      State.INVALID
  }

  /**
   * Right shift operation.
   */
  function method {:verify false} Shr(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var lhs := st.Peek(0);
      var rhs := st.Peek(1) as bv256;
      // NOTE: unclear whether shifting is optimal choice here.
      var res := if lhs < 256 then (rhs >> lhs) else 0;
      st.Pop().Pop().Push(res as u256).Next()
    else
      State.INVALID
  }

  /**
   * Get input data from the current environment.
   */
  function method CallDataLoad(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 1
      then
      var loc := st.Peek(0);
      var val := if loc >= Context.DataSize(st.evm.context) then 0
        else Context.DataRead(st.evm.context,loc);
      st.Pop().Push(val).Next()
    else
      State.INVALID
  }

  /**
   * Get size of input data in current environment.
   */
  function method CallDataSize(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Capacity() >= 1
      then
      var len := |st.evm.context.calldata|;
      st.Push(len as u256).Next()
    else
      State.INVALID
  }

  /**
   * Get size of input data in current environment.
   */
  function method CallDataCopy(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 3
      then
      var m_loc := st.Peek(0);
      var d_loc := st.Peek(1);
      var len := st.Peek(2);
      // NOTE: This condition is not specified in the yellow paper.
      // Its not clear whether that was intended or not.  However, its
      // impossible to trigger this in practice (due to the gas costs
      // involved).
      if (m_loc as int) + (len as int) < MAX_U256
      then
        // Slice bytes out of call data (with padding as needed)
        var data := Context.DataSlice(st.evm.context,d_loc,len);
        // Sanity check
        assert |data| == (len as int);
        // Copy slice into memory
        st.Pop().Pop().Pop().Copy(m_loc,data).Next()
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Pop word from stack.
   */
  function method Pop(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 1
    then
      st.Pop().Next()
    else
      State.INVALID
  }

  /**
   * Get word from memory.
   */
  function method MLoad(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 1
      then
      var loc := st.Peek(0);
      // NOTE: This condition is not specified in the yellow paper.
      // Its not clear whether that was intended or not.  However, its
      // impossible to trigger this in practice (due to the gas costs
      // involved).
      if (loc as int) + 31 <= MAX_U256
        then
        var val := st.Read(loc);
        // Write big endian order
        st.Pop().Push(val).Next()
      else
        State.INVALID
    else
      State.INVALID
  }


  /**
   * Save word to memory.
   */
  function method MStore(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var loc := st.Peek(0);
      var val := st.Peek(1);
      // NOTE: This condition is not specified in the yellow paper.
      // Its not clear whether that was intended or not.  However, its
      // impossible to trigger this in practice (due to the gas costs
      // involved).
      if (loc as int) + 31 <= MAX_U256
        then
        // Write big endian order
        st.Pop().Pop().Write(loc,val).Next()
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Save byte to memory.
   */
  function method MStore8(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var loc := st.Peek(0);
      var val := (st.Peek(1) % 256) as u8;
      if (loc as int) < MAX_U256
        then
        // Write byte
        st.Pop().Pop().Write8(loc,val).Next()
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Get word from storage.
   */
  function method SLoad(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 1
      then
      var loc := st.Peek(0);
      var val := st.Load(loc);
      // Push word
      st.Pop().Push(val).Next()
    else
      State.INVALID
  }

  /**
   * Save word to storage.
   */
  function method SStore(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var loc := st.Peek(0);
      var val := st.Peek(1);
      // Store word
      st.Pop().Pop().Store(loc,val).Next()
    else
      State.INVALID
  }

  /**
   * Unconditional branch.
   */
  function method Jump(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 1
      then
      var pc := st.Peek(0);
      // Check valid branch target
      if st.IsJumpDest(pc)
      then
        st.Pop().Goto(pc)
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Unconditional branch.
   */
  function method JumpI(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      var pc := st.Peek(0);
      var val := st.Peek(1);
      // Check branch taken or not
      if val == 0 then st.Pop().Pop().Next()
      // Check valid branch target
      else if st.IsJumpDest(pc)
      then
        st.Pop().Pop().Goto(pc)
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Gets value of program counter prior to this instruction being executed.
   */
  function method Pc(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Capacity() >= 1
    then
      st.Push(st.PC()).Next()
    else
      State.INVALID
  }

  /**
   * Marks a valid destination for a jump, but otherwise has no effect
   * on machine state.
   */
  function method JumpDest(st: State) : State
  requires !st.IsFailure() {
    st.Next()
  }

  /**
   * Push one byte onto stack.
   */
  function method Push1(st: State, k: u8) : State
  requires !st.IsFailure() {
    //
    if st.Capacity() >= 1
      then
      st.Push(k as u256).Skip(2)
    else
      State.INVALID
  }

  /**
   * Push two bytes onto stack.
   */
  function method Push2(st: State, k: u16) : State
  requires !st.IsFailure() {
    //
    if st.Capacity() >= 1
      then
      st.Push(k as u256).Skip(3)
    else
      State.INVALID
  }

  /**
   * Duplicate item on stack.
   */
  function method Dup(st: State, k: nat) : State
  requires !st.IsFailure()
  requires k > 0 {
    //
    if st.Operands() > (k-1) && st.Capacity() >= 1
      then
      var kth := st.Peek(k-1);
      st.Push(kth).Next()
    else
      State.INVALID
  }

  /**
   * Swap two items on the stack
   */
  function method Swap(st: State, k: nat) : State
  requires !st.IsFailure() {
    //
    if st.Operands() > k
      then
      st.Swap(k).Next()
    else
      State.INVALID
  }

  /**
   * Halt execution returning output data.
   */
  function method Return(st: State) : State
  requires !st.IsFailure() {
    //
    if st.Operands() >= 2
      then
      // Determine amount of data to return.
      var len := st.Peek(1) as int;
      var start := st.Peek(0) as int;
      // Sanity check bounds
      if (start+len) <= MAX_U256
      then
        // Read out that data.
        var data := Memory.Slice(st.evm.memory, start as u256, len);
        // Done
        State.RETURNS(gas:=st.evm.gas,data:=data)
      else
        State.INVALID
    else
      State.INVALID
  }

  /**
   * Revert execution returning output data.
   */
  function method Revert(st: State) : State
  requires !st.IsFailure() {

    //
    if st.Operands() >= 2
      then
      // Determine amount of data to return.
      var len := st.Peek(1) as int;
      var start := st.Peek(0) as int;
      // Sanity check bounds
      if (start+len) <= MAX_U256
      then
        // Read out that data.
        var data := Memory.Slice(st.evm.memory, start as u256, len);
        // Done
        State.REVERTS(gas:=st.evm.gas,data:=data)
      else
        State.INVALID
    else
      State.INVALID
  }

  // =============================================================================
  // Microcode
  // =============================================================================

  /**
   * Unsigned integer division with handling for zero.
   */
  function method DivWithZero(lhs:u256, rhs:u256) : u256 {
    if rhs == 0 then 0 as u256
    else
      (lhs / rhs) as u256
  }

  /**
   * Unsigned integer remainder with handling for zero.
   */
  function method ModWithZero(lhs:u256, rhs:u256) : u256 {
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
  function method SDivWithZero(lhs:i256, rhs:i256) : i256 {
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
  function method SModWithZero(lhs:i256, rhs:i256) : i256 {
    if rhs == 0 then 0 as i256
    else
      // Do not use Dafny's remainder operator here!
      I256.Rem(lhs,rhs)
  }
}
