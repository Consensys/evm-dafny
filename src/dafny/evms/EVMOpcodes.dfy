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

include "../util/NativeTypes.dfy" 

/** Opcodes from David's branch. */
module EVMOpcodes {

    import opened NativeTypes

    // 0s: Stop and Arithmetic Operations
	const STOP : uint8 := 0x0; 
	const ADD : uint8 := 0x01;
	const MUL : uint8 := 0x02; 
	const SUB : uint8 := 0x03;
	const DIV : uint8 := 0x04;
	const SDIV : uint8 := 0x05;
	const MOD : uint8 := 0x06;
	const SMOD : uint8 := 0x07;
	const ADDMOD : uint8 := 0x08;
	const MULMOD : uint8 := 0x09;
	const EXP : uint8 := 0x0a;
	const SIGNEXTEND : uint8 := 0x0b;
	// 10s: Comparison & Bitwise Logic Operations
	const LT : uint8 := 0x10;
	const GT : uint8 := 0x11;
	const SLT : uint8 := 0x12;
	const SGT : uint8 := 0x13;
	const EQ : uint8 := 0x14;
	const ISZERO : uint8 := 0x15;
	const AND : uint8 := 0x16;
	const OR : uint8 := 0x17;
	const XOR : uint8 := 0x18;
	const NOT : uint8 := 0x19;
	const BYTE : uint8 := 0x1a;

    // 20s: SHA3
	const SHA3 : uint8 := 0x20;
	// 30s: Environment Information
	const ADDRESS : uint8 := 0x30;
	const BALANCE : uint8 := 0x31;
	const ORIGIN : uint8 := 0x32;
	const CALLER : uint8 := 0x33;
	const CALLVALUE : uint8 := 0x34;
	const CALLDATALOAD : uint8 := 0x35;
	const CALLDATASIZE : uint8 := 0x36;
	const CALLDATACOPY : uint8 := 0x37;
	const CODESIZE : uint8 := 0x38;
	const CODECOPY : uint8 := 0x39;
	const GASPRICE : uint8 := 0x3a;
	const EXTCODESIZE : uint8 := 0x3b;
	const EXTCODECOPY : uint8 := 0x3c;
	const RETURNDATASIZE : uint8 := 0x3d;
	const RETURNDATACOPY : uint8 := 0x3e;
	// 40s: Block Information
	const BLOCKHASH : uint8 := 0x40;
	const COINBASE : uint8 := 0x41;
	const TIMESTAMP : uint8 := 0x42;
	const NUMBER : uint8 := 0x43;
	const DIFFICULTY : uint8 := 0x44;
	const GASLIMIT : uint8 := 0x45;
	// 50s: Stack, Memory Storage and Flow Operations
	const POP : uint8 := 0x50;
	const MLOAD : uint8 := 0x51;
	const MSTORE : uint8 := 0x52;
	const MSTORE8 : uint8 := 0x53;
	const SLOAD : uint8 := 0x54;
	const SSTORE : uint8 := 0x55;
	const JUMP : uint8 := 0x56;
	const JUMPI : uint8 := 0x57;
	const PC : uint8 := 0x58;
	const MSIZE : uint8 := 0x59;
	const GAS : uint8 := 0x5a;
	const JUMPDEST : uint8 := 0x5b;
	// 60s & 70s: Push Operations
	const PUSH1 : uint8 := 0x60;
	const PUSH2 : uint8 := 0x61;
	const PUSH3 : uint8 := 0x62;
	const PUSH4 : uint8 := 0x63;
	const PUSH5 : uint8 := 0x64;
	const PUSH6 : uint8 := 0x65;
	const PUSH7 : uint8 := 0x66;
	const PUSH8 : uint8 := 0x67;
	const PUSH9 : uint8 := 0x68;
	const PUSH10 : uint8 := 0x69;
	const PUSH11 : uint8 := 0x6a;
	const PUSH12 : uint8 := 0x6b;
	const PUSH13 : uint8 := 0x6c;
	const PUSH14 : uint8 := 0x6d;
	const PUSH15 : uint8 := 0x6e;
	const PUSH16 : uint8 := 0x6f;
	const PUSH17 : uint8 := 0x70;
	const PUSH18 : uint8 := 0x71;
	const PUSH19 : uint8 := 0x72;
	const PUSH20 : uint8 := 0x73;
	const PUSH21 : uint8 := 0x74;
	const PUSH22 : uint8 := 0x75;
	const PUSH23 : uint8 := 0x76;
	const PUSH24 : uint8 := 0x77;
	const PUSH25 : uint8 := 0x78;
	const PUSH26 : uint8 := 0x79;
	const PUSH27 : uint8 := 0x7a;
	const PUSH28 : uint8 := 0x7b;
	const PUSH29 : uint8 := 0x7c;
	const PUSH30 : uint8 := 0x7d;
	const PUSH31 : uint8 := 0x7e;
	const PUSH32 : uint8 := 0x7f;
	// 80s: Duplication Operations
	const DUP1 : uint8 := 0x80;
	const DUP2 : uint8 := 0x81;
	const DUP3 : uint8 := 0x82;
	const DUP4 : uint8 := 0x83;
	const DUP5 : uint8 := 0x84;
	const DUP6 : uint8 := 0x85;
	const DUP7 : uint8 := 0x86;
	const DUP8 : uint8 := 0x87;
	const DUP9 : uint8 := 0x88;
	const DUP10 : uint8 := 0x89;
	const DUP11 : uint8 := 0x8a;
	const DUP12 : uint8 := 0x8b;
	const DUP13 : uint8 := 0x8c;
	const DUP14 : uint8 := 0x8d;
	const DUP15 : uint8 := 0x8e;
	const DUP16 : uint8 := 0x8f;
	// 90s: Exchange Operations
	const SWAP1 : uint8 := 0x90;
	const SWAP2 : uint8 := 0x91;
	const SWAP3 : uint8 := 0x92;
	const SWAP4 : uint8 := 0x93;
	const SWAP5 : uint8 := 0x94;
	const SWAP6 : uint8 := 0x95;
	const SWAP7 : uint8 := 0x96;
	const SWAP8 : uint8 := 0x97;
	const SWAP9 : uint8 := 0x98;
	const SWAP10 : uint8 := 0x99;
	const SWAP11 : uint8 := 0x9a;
	const SWAP12 : uint8 := 0x9b;
	const SWAP13 : uint8 := 0x9c;
	const SWAP14 : uint8 := 0x9d;
	const SWAP15 : uint8 := 0x9e;
	const SWAP16 : uint8 := 0x9f;
	// a0s: Logging Operations
	const LOG0 : uint8 := 0xa0;
	const LOG1 : uint8 := 0xa1;
	const LOG2 : uint8 := 0xa2;
	const LOG3 : uint8 := 0xa3;
	const LOG4 : uint8 := 0xa4;
	// f0s: System operations
	const CREATE : uint8 := 0xf0;
	const CALL : uint8 := 0xf1;
	const CALLCODE : uint8 := 0xf2;
	const RETURN : uint8 := 0xf3;
	const DELEGATECALL : uint8 := 0xf4;
	const STATICCALL : uint8 := 0xfa;
	const REVERT : uint8 := 0xfd;
	const INVALID : uint8 := 0xfe;
	const SELFDESTRUCT : uint8 := 0xff;
}
