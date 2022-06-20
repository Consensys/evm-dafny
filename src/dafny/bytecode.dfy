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

/**
 * Defines semantics for the various EVM bytecodes.
 */
module Bytecode {
    import opened Int

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
	const STOP : int := 0x0;
	const ADD : int := 0x01;
	const MUL : int := 0x02;
	const SUB : int := 0x03;
	const DIV : int := 0x04;
	const SDIV : int := 0x05;
	const MOD : int := 0x06;
	const SMOD : int := 0x07;
	const ADDMOD : int := 0x08;
	const MULMOD : int := 0x09;
	const EXP : int := 0x0a;
	const SIGNEXTEND : int := 0x0b;
	// 10s: Comparison & Bitwise Logic Operations
	const LT : int := 0x10;
	const GT : int := 0x11;
	const SLT : int := 0x12;
	const SGT : int := 0x13;
	const EQ : int := 0x14;
	const ISZERO : int := 0x15;
	const AND : int := 0x16;
	const OR : int := 0x17;
	const XOR : int := 0x18;
	const NOT : int := 0x19;
	const BYTE : int := 0x1a;
	// 20s: SHA3
	const SHA3 : int := 0x20;
	// 30s: Environment Information
	const ADDRESS : int := 0x30;
	const BALANCE : int := 0x31;
	const ORIGIN : int := 0x32;
	const CALLER : int := 0x33;
	const CALLVALUE : int := 0x34;
	const CALLDATALOAD : int := 0x35;
	const CALLDATASIZE : int := 0x36;
	const CALLDATACOPY : int := 0x37;
	const CODESIZE : int := 0x38;
	const CODECOPY : int := 0x39;
	const GASPRICE : int := 0x3a;
	const EXTCODESIZE : int := 0x3b;
	const EXTCODECOPY : int := 0x3c;
	const RETURNDATASIZE : int := 0x3d;
	const RETURNDATACOPY : int := 0x3e;
	// 40s: Block Information
	const BLOCKHASH : int := 0x40;
	const COINBASE : int := 0x41;
	const TIMESTAMP : int := 0x42;
	const NUMBER : int := 0x43;
	const DIFFICULTY : int := 0x44;
	const GASLIMIT : int := 0x45;
	// 50s: Stack, Memory Storage and Flow Operations
	const POP : int := 0x50;
	const MLOAD : int := 0x51;
	const MSTORE : int := 0x52;
	const MSTORE8 : int := 0x53;
	const SLOAD : int := 0x54;
	const SSTORE : int := 0x55;
	const JUMP : int := 0x56;
	const JUMPI : int := 0x57;
	const PC : int := 0x58;
	const MSIZE : int := 0x59;
	const GAS : int := 0x5a;
	const JUMPDEST : int := 0x5b;
	// 60s & 70s: Push Operations
	const PUSH1 : int := 0x60;
	const PUSH2 : int := 0x61;
	const PUSH3 : int := 0x62;
	const PUSH4 : int := 0x63;
	const PUSH5 : int := 0x64;
	const PUSH6 : int := 0x65;
	const PUSH7 : int := 0x66;
	const PUSH8 : int := 0x67;
	const PUSH9 : int := 0x68;
	const PUSH10 : int := 0x69;
	const PUSH11 : int := 0x6a;
	const PUSH12 : int := 0x6b;
	const PUSH13 : int := 0x6c;
	const PUSH14 : int := 0x6d;
	const PUSH15 : int := 0x6e;
	const PUSH16 : int := 0x6f;
	const PUSH17 : int := 0x70;
	const PUSH18 : int := 0x71;
	const PUSH19 : int := 0x72;
	const PUSH20 : int := 0x73;
	const PUSH21 : int := 0x74;
	const PUSH22 : int := 0x75;
	const PUSH23 : int := 0x76;
	const PUSH24 : int := 0x77;
	const PUSH25 : int := 0x78;
	const PUSH26 : int := 0x79;
	const PUSH27 : int := 0x7a;
	const PUSH28 : int := 0x7b;
	const PUSH29 : int := 0x7c;
	const PUSH30 : int := 0x7d;
	const PUSH31 : int := 0x7e;
	const PUSH32 : int := 0x7f;
	// 80s: Duplication Operations
	const DUP1 : int := 0x80;
	const DUP2 : int := 0x81;
	const DUP3 : int := 0x82;
	const DUP4 : int := 0x83;
	const DUP5 : int := 0x84;
	const DUP6 : int := 0x85;
	const DUP7 : int := 0x86;
	const DUP8 : int := 0x87;
	const DUP9 : int := 0x88;
	const DUP10 : int := 0x89;
	const DUP11 : int := 0x8a;
	const DUP12 : int := 0x8b;
	const DUP13 : int := 0x8c;
	const DUP14 : int := 0x8d;
	const DUP15 : int := 0x8e;
	const DUP16 : int := 0x8f;
	// 90s: Exchange Operations
	const SWAP1 : int := 0x90;
	const SWAP2 : int := 0x91;
	const SWAP3 : int := 0x92;
	const SWAP4 : int := 0x93;
	const SWAP5 : int := 0x94;
	const SWAP6 : int := 0x95;
	const SWAP7 : int := 0x96;
	const SWAP8 : int := 0x97;
	const SWAP9 : int := 0x98;
	const SWAP10 : int := 0x99;
	const SWAP11 : int := 0x9a;
	const SWAP12 : int := 0x9b;
	const SWAP13 : int := 0x9c;
	const SWAP14 : int := 0x9d;
	const SWAP15 : int := 0x9e;
	const SWAP16 : int := 0x9f;
	// a0s: Logging Operations
	const LOG0 : int := 0xa0;
	const LOG1 : int := 0xa1;
	const LOG2 : int := 0xa2;
	const LOG3 : int := 0xa3;
	const LOG4 : int := 0xa4;
	// f0s: System operations
	const CREATE : int := 0xf0;
	const CALL : int := 0xf1;
	const CALLCODE : int := 0xf2;
	const RETURN : int := 0xf3;
	const DELEGATECALL : int := 0xf4;
	const STATICCALL : int := 0xfa;
	const REVERT : int := 0xfd;
	const INVALID : int := 0xfe;
	const SELFDESTRUCT : int := 0xff;
}
