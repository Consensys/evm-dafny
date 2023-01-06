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

module Opcode {
    import opened Int

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
	const KECCAK256 : u8 := 0x20;
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
    const EXTCODEHASH : u8 := 0x3f;
	// 40s: Block Information
	const BLOCKHASH : u8 := 0x40;
	const COINBASE : u8 := 0x41;
	const TIMESTAMP : u8 := 0x42;
	const NUMBER : u8 := 0x43;
	const DIFFICULTY : u8 := 0x44;
	const GASLIMIT : u8 := 0x45;
    const CHAINID : u8 := 0x46;
    const SELFBALANCE : u8 := 0x47;
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
    // e0s
    const EOF : u8 := 0xef;
	// f0s: System operations
	const CREATE : u8 := 0xf0;
	const CALL : u8 := 0xf1;
	const CALLCODE : u8 := 0xf2;
	const RETURN : u8 := 0xf3;
	const DELEGATECALL : u8 := 0xf4;
    const CREATE2 : u8 := 0xf5;
	const STATICCALL : u8 := 0xfa;
	const REVERT : u8 := 0xfd;
	const INVALID : u8 := 0xfe;
    const SELFDESTRUCT : u8 := 0xff;

	/**
     *  Decode an opcode.
     */
    function method Decode(k: u8): string
    {
        match k 
            // 0s: Stop and Arithmetic Operations
            case 0x00 => "STOP"
            case 0x01 => "ADD"
            case 0x02 => "MUL"
            case 0x03 => "SUB"
            case 0x04 => "DIV"
            case 0x05 => "SDIV"
            case 0x06 => "MOD"
            case 0x07 => "SMOD"
            case 0x08 => "ADDMOD"
            case 0x09 => "MULMOD"
            case 0x0a => "EXP"
            case 0x0b => "SIGNEXTEND"

            // 10s: Comparison & Bitwise Logic Operations
            case 0x10 => "LT"
            case 0x11 => "GT"
            case 0x12 => "SLT"
            case 0x13 => "SGT"
            case 0x14 => "EQ"
            case 0x15 => "ISZERO"
            case 0x16 => "AND"
            case 0x17 => "OR"
            case 0x18 => "XOR"
            case 0x19 => "NOT"
            case 0x1a => "BYTE"
            case 0x1b => "SHL"
            case 0x1c => "SHR"
            case 0x1d => "SAR"

            // 20s: SHA3
            case 0x20 => "KECCAK256"

            // 30s: Environment Information
            case 0x30 => "ADDRESS"
            case 0x31 => "BALANCE"
            case 0x32 => "ORIGIN"
            case 0x33 => "CALLER"
            case 0x34 => "CALLVALUE"
            case 0x35 => "CALLDATALOAD"
            case 0x36 => "CALLDATASIZE"
            case 0x37 => "CALLDATACOPY"
            case  0x38 => "CODESIZE"
            case  0x39 => "CODECOPY"
            case  0x3a => "GASPRICE"
            case 0x3b => "EXTCODESIZE"
            case 0x3c => "EXTCODECOPY"
            case 0x3d => "RETURNDATASIZE"
            case 0x3e => "RETURNDATACOPY"
            case 0x3f => "EXTCODEHASH"

            // 40s: Block Information
            case 0x40 => "BLOCKHASH"
            case 0x41 => "COINBASE"
            case 0x42 => "TIMESTAMP"
            case 0x43 => "NUMBER"
            case 0x44 => "DIFFICULTY"
            case 0x45 => "GASLIMIT"
            case 0x46 => "CHAINID"
            case 0x47 => "SELFBALANCE"

            // 50s: Stack, Memory Storage and Flow Operations
            case  0x50 => "POP"
            case  0x51 => "MLOAD"
            case  0x52 => "MSTORE"
            case  0x53 => "MSTORE8"
            case  0x54 => "SLOAD"
            case  0x55 => "SSTORE"
            case  0x56 => "JUMP"
            case  0x57 => "JUMPI"
            case  0x58 => "PC"
            case  0x59 => "MSIZE"
            case  0x5a => "GAS"
            case  0x5b => "JUMPDEST"

            // 60s & 70s: Push Operations
            case 0x60 => "PUSH1"
            case 0x61 => "PUSH2"
            case 0x62 => "PUSH3"
            case 0x63 => "PUSH4"
            case 0x64 => "PUSH5"
            case 0x65 => "PUSH6"
            case 0x66 => "PUSH7"
            case 0x67 => "PUSH8"
            case 0x68 => "PUSH9"
            case 0x69 => "PUSH10"
            case 0x6a => "PUSH11"
            case 0x6b => "PUSH12"
            case 0x6c => "PUSH13"
            case 0x6d => "PUSH14"
            case 0x6e => "PUSH15"
            case 0x6f => "PUSH16"
            case 0x70 => "PUSH17"
            case 0x71 => "PUSH18"
            case 0x72 => "PUSH19"
            case 0x73 => "PUSH20"
            case 0x74 => "PUSH21"
            case 0x75 => "PUSH22"
            case 0x76 => "PUSH23"
            case 0x77 => "PUSH24"
            case 0x78 => "PUSH25"
            case 0x79 => "PUSH26"
            case 0x7a => "PUSH27"
            case 0x7b => "PUSH28"
            case 0x7c => "PUSH29"
            case 0x7d => "PUSH30"
            case 0x7e => "PUSH31"
            case 0x7f => "PUSH32"

            // 80s: Duplication Operations
            case 0x80 => "DUP1"
            case 0x81 => "DUP2"
            case 0x82 => "DUP3"
            case 0x83 => "DUP4"
            case 0x84 => "DUP5"
            case 0x85 => "DUP6"
            case 0x86 => "DUP7"
            case 0x87 => "DUP8"
            case 0x88 => "DUP9"
            case 0x89 => "DUP10"
            case 0x8a => "DUP11"
            case 0x8b => "DUP12"
            case 0x8c => "DUP13"
            case 0x8d => "DUP14"
            case 0x8e => "DUP15"
            case 0x8f => "DUP16"

            // 90s: Exchange Operations
            case 0x90 => "SWAP1"
            case 0x91 => "SWAP2"
            case 0x92 => "SWAP3"
            case 0x93 => "SWAP4"
            case 0x94 => "SWAP5"
            case 0x95 => "SWAP6"
            case 0x96 => "SWAP7"
            case 0x97 => "SWAP8"
            case 0x98 => "SWAP9"
            case 0x99 => "SWAP10"
            case 0x9a => "SWAP11"
            case 0x9b => "SWAP12"
            case 0x9c => "SWAP13"
            case 0x9d => "SWAP14"
            case 0x9e => "SWAP15"
            case 0x9f => "SWAP16"

            // a0s: Logging Operations
            case 0xa0 => "LOG0"
            case 0xa1 => "LOG1"
            case 0xa2 => "LOG2"
            case 0xa3 => "LOG3"
            case 0xa4 => "LOG4"

            // e0s
            case 0xef => "EOF"

            // f0s: System operations
            case 0xf0 => "CREATE"
            case 0xf1 => "CALL"
            case 0xf2 => "CALLCODE"
            case 0xf3 => "RETURN"
            case 0xf4 => "DELEGATECALL"
            case 0xf5 => "CREATE2"
            case 0xfa => "STATICCALL"
            case 0xfd => "REVERT"
            case 0xfe => "INVALID"
            case 0xff => "SELFDESTRUCT"

            case _ => "NA"
    }

}
