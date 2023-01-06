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

include "./disassembler.dfy"
include "./util/string.dfy"
include "./opcodes.dfy"

import opened Dissassembler
import opened StringHelper 
import opened Int 
import opened Opcode

/* The betting bytecode. */
const p1: string := "60808060405260043610608f576000803560e01c63310bd74b8114602b5763d4b839928114606b57608c565b34156034578182fd5b6020600319360112156044578182fd5b600435670de0b6b3a7640000811115605a578283fd5b8254156064578283fd5b8083558283f35b34156074578182fd5b81600319360112156083578182fd5b81548352602083f35b50505b600080fd"
    /* 
    A very simple code:  0001603a63b1c2d4ff

    Betting binary: [note: we have to make sure that each u8 is written with 2 chars, which means
    left padding with 0 things like c or 1]
    0x60, 0x80, 0x60, 0x40, 0x52, 0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x60, 0x00, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x11, 0x61, 0x0c, 0x25, 0x14, 0x60, 0x2b, 0x57, 0x80, 0x63, 0xd4, 0xb8, 0x39, 0x92, 0x14, 0x60, 0x33, 0x57, 0x5b, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x60, 0x31, 0x60, 0x59, 0x56, 0x5b, 0x00, 0x5b, 0x34, 0x80, 0x15, 0x60, 0x3e, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x50, 0x60, 0x47, 0x60, 0x00, 0x54, 0x81, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x90, 0x81, 0x52, 0x60, 0x20, 0x01, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b, 0x60, 0x00, 0x54, 0x34, 0x11, 0x15, 0x60, 0x67, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x60, 0x00, 0x80, 0x54, 0x34, 0x90, 0x03, 0x90, 0x55, 0x56, 0xfe, 0xa2, 0x64, 0x69, 0x70, 0x66, 0x73, 0x58, 0x22, 0x12, 0x20, 0x50, 0x22, 0x33, 0xad, 0x5c, 0x06, 0x77, 0x75, 0x8a, 0xba, 0x64, 0xa4, 0xde, 0x67, 0x63, 0xe5, 0xfe, 0x40, 0xa1, 0xb8, 0x02, 0x84, 0x8b, 0xf3, 0x61, 0xde, 0x2b, 0x86, 0x4a, 0xae, 0x24, 0x96, 0x64, 0x73, 0x6f, 0x6c, 0x63, 0x43, 0x00, 0x08, 0x11, 0x00, 0x33

    and as string:
    60806040526004361060265760003560e01c806311610c2514602b578063d4b83992146033575b600080fd5b60316059565b005b348015603e57600080fd5b50604760005481565b60405190815260200160405180910390f35b600054341115606757600080fd5b60008054349003905556fea2646970667358221220502233ad5c0677758aba64a4de6763e5fe40a1b802848bf361de2b864aae249664736f6c63430008110033

    Note in the result that the code after INVALID is not reachable and seems to be garbage.
    */

/**
*  Dissassemble.
*
*  Usage: 
*    dafny /noVerify /compile:4 '/Users/franck/development/evm-dafny/src/dafny/disassembler.dfy' --args "0001603a63b1c2d4f0" 
*/
method {:verify true} mMain(argv: seq<string>)
{
    if |argv| < 2 {
        print "error\n";
        print "Usage: dafny /noVerify /compile:4 progWithMain --args \"bytecode as string\"\n";
    } else if |argv[1]| % 2 == 0  {
        //  Check that it is an Hex String
        if IsHexString(argv[1]) {
            var s := Dis(argv[1]);
            for i: nat := 0 to |s| {
                print s[i];
            }
        } else {
            print "error not hex string\n";
        }
    } else {
        print "error not even number of characters\n";
    }
}

method {:verify true} Main(argv: seq<string>)
{
    if |argv| < 2 {
        print "error\n";
        print "Usage: dafny /noVerify /compile:4 progWithMain --args \"bytecode as string\"\n";
    } else if |argv[1]| % 2 == 0  {
        //  Check that it is an Hex String
        if IsHexString(argv[1]) {
            var s := EVMProg(Dis2(argv[1]));
            print s.PrintAsSeq(), "\n";
            for i: nat := 0 to |s.PrettyPrint()| {
                print s.PrettyPrint()[i], "\n";
            }
        } else {
            print "error not hex string\n";
        }
    } else {
        print "error not even number of characters\n";
    }
}

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

method {:verify true} Main2(argv: seq<string>)
{
   var a := Assemble(BYTECODE);
   print a, "\n";
}