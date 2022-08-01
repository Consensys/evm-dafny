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
 include "opcodes.dfy"
 include "state.dfy"

module Gas {
 
	import opened Opcode
	import opened EvmState
    import opened Int
	
    const G_ZERO: nat := 0;
	const G_BASE: nat := 2;
	const G_VERYLOW: nat := 3;
	const G_LOW: nat := 5;
	const G_MID: nat := 8;
	const G_HIGH: nat := 10;
	const G_EXTCODE: nat := 700;
	const G_BALANCE: nat := 400;
	const G_SLOAD: nat := 200;
	const G_JUMPDEST: nat := 1;
	const G_SSET: nat := 20000;
	const G_SRESET: nat := 5000;
	const R_SCLEAR: nat := 15000;
	const R_SELFDESTRUCT: nat := 24000;
	const G_SELFDESTRUCT: nat := 5000;
	const G_CREATE: nat := 32000;
	const G_CODEDEPOSIT: nat := 200;
	const G_CALL: nat := 700;
	const G_CALLVALUE: nat := 9000;
	const G_CALLSTIPEND: nat := 2300;
	const G_NEWACCOUNT: nat := 25000;
	const G_EXP: nat := 10;
	const G_EXPBYTE: nat := 50;
	const G_MEMORY: nat := 3;
	const G_TXCREATE: nat := 32000;
	const G_TXDATAZERO: nat := 4;
	const G_TXDATANONZERO: nat := 68;
	const G_TRANSACTION: nat := 21000;
	const G_LOG: nat := 375;
	const G_LOGDATA: nat := 8;
	const G_LOGTOPIC: nat := 375;
	const G_SHA3: nat := 30;
	const G_SHA3WORD: nat := 6;
	const G_COPY: nat := 3;
	const G_BLOCKHASH: nat := 20;
	const G_QUADDIVISOR: nat := 100;

   

	/** The constant Gas cost for each  */ 
    const GAS_ONE: map<u8, OKState -> nat> := map[     
        STOP := (s:OKState) => 1 as nat, 
        ADD := (s:OKState) => 1, 
        MUL := (s:OKState) => 1, 
        SUB := (s:OKState) => 1, 
        DIV := (s:OKState) => 1, 
        SDIV := (s:OKState) => 1, 
        MOD := (s:OKState) => 1, 
        SMOD := (s:OKState) => 1, 
        ADDMOD := (s:OKState) => 1, 
        MULMOD := (s:OKState) => 1, 
        EXP := (s:OKState) => 1, 
        SIGNEXTEND := (s:OKState) => 1, 
        // 0x10s: Comparison & Bitwise Logic
        LT := (s:OKState) => 1, 
        GT := (s:OKState) => 1, 
        SLT := (s:OKState) => 1, 
        SGT := (s:OKState) => 1, 
        EQ := (s:OKState) => 1, 
        ISZERO := (s:OKState) => 1, 
        AND := (s:OKState) => 1, 
        OR := (s:OKState) => 1, 
        XOR := (s:OKState) => 1, 
        NOT := (s:OKState) => 1, 
        BYTE := (s:OKState) => 1, 
        SHL := (s:OKState) => 1, 
        SHR := (s:OKState) => 1, 
        SAR := (s:OKState) => 1, 
        // 0x20s
        //  KECCAK256 := (s:OKState) => 1, 
        // 0x30s: Environment Information
        ADDRESS := (s:OKState) => 1, 
        BALANCE := (s:OKState) => 1, 
        ORIGIN := (s:OKState) => 1, 
        CALLER := (s:OKState) => 1, 
        CALLVALUE := (s:OKState) => 1, 
        CALLDATALOAD := (s:OKState) => 1, 
        CALLDATASIZE := (s:OKState) => 1, 
        CALLDATACOPY := (s:OKState) => 1, 
        CODESIZE := (s:OKState) => 1, 
        CODECOPY := (s:OKState) => 1, 
        GASPRICE := (s:OKState) => 1, 
        EXTCODESIZE := (s:OKState) => 1, 
        EXTCODECOPY := (s:OKState) => 1, 
        RETURNDATASIZE := (s:OKState) => 1, 
        RETURNDATACOPY := (s:OKState) => 1, 
        //  EXTCODEHASH := (s:OKState) => 1, 
        // 0x40s: Block Information
        BLOCKHASH := (s:OKState) => 1, 
        COINBASE := (s:OKState) => 1, 
        TIMESTAMP := (s:OKState) => 1, 
        NUMBER := (s:OKState) => 1, 
        DIFFICULTY := (s:OKState) => 1, 
        GASLIMIT := (s:OKState) => 1, 
        //  CHAINID := (s:OKState) => 1, 
        //  SELFBALANCE := (s:OKState) => 1, 
        // 0x50s: Stack, Memory, Storage and Flow
        POP := (s:OKState) => 1, 
        MLOAD := (s:OKState) => 1, 
        MSTORE := (s:OKState) => 1, 
        MSTORE8 := (s:OKState) => 1, 
        SLOAD := (s:OKState) => 1, 
        SSTORE := (s:OKState) => 1, 
        JUMP := (s:OKState) => 1, 
        JUMPI := (s:OKState) => 1, 
        PC := (s:OKState) => 1,
        JUMPDEST := (s:OKState) => 1, 
        // 0x60s & 0x70s: Push operations
        PUSH1 := (s: OKState) => 1,
        PUSH2 := (s:OKState) => 1,
        // 0x80s: Duplicate operations
        DUP1 := (s:OKState) => 1, 
        DUP2 := (s:OKState) => 1, 
        DUP3 := (s:OKState) => 1, 
        DUP4 := (s:OKState) => 1, 
        DUP5 := (s:OKState) => 1, 
        DUP6 := (s:OKState) => 1, 
        DUP7 := (s:OKState) => 1, 
        DUP8 := (s:OKState) => 1, 
        DUP9 := (s:OKState) => 1, 
        DUP10 := (s:OKState) => 1, 
        DUP11 := (s:OKState) => 1, 
        DUP12 := (s:OKState) => 1, 
        DUP13 := (s:OKState) => 1, 
        DUP14 := (s:OKState) => 1, 
        DUP15 := (s:OKState) => 1, 
        DUP16 := (s:OKState) => 1, 
        // 0x90s: Exchange operations
        SWAP1 := (s:OKState) => 1, 
        SWAP2 := (s:OKState) => 1, 
        SWAP3 := (s:OKState) => 1, 
        SWAP4 := (s:OKState) => 1, 
        SWAP5 := (s:OKState) => 1, 
        SWAP6 := (s:OKState) => 1, 
        SWAP7 := (s:OKState) => 1, 
        SWAP8 := (s:OKState) => 1, 
        SWAP9 := (s:OKState) => 1, 
        SWAP10 := (s:OKState) => 1, 
        SWAP11 := (s:OKState) => 1, 
        SWAP12 := (s:OKState) => 1, 
        SWAP13 := (s:OKState) => 1, 
        SWAP14 := (s:OKState) => 1, 
        SWAP15 := (s:OKState) => 1, 
        SWAP16 := (s:OKState) => 1, 
        // 0xA0s: Log operations
        // else if LOG0 <=opcode <= LOG4 := (s:OKState)
        //   var k := opcode - LOG0) as int; evalLOG(st,k),
        // 0xf0
        CREATE := (s:OKState) => 1, 
        CALL := (s:OKState) => 1, 
        CALLCODE := (s:OKState) => 1, 
        RETURN := (s:OKState) => 1, 
        DELEGATECALL := (s:OKState) => 1, 
        // CREATE2 := (s:OKState) => 1, 
        STATICCALL := (s:OKState) => 1, 
        REVERT := (s:OKState) => 1,
        SELFDESTRUCT := (s:OKState) => 1
    ]  
	
	/**	The Berlin gas cost function. 
	 *
	 * see H.1 page 29, BERLIN VERSION 3078285 – 2022-07-13.
	 */
    const GAS_BERLIN: map<u8, OKState -> nat> := map[     
        STOP := (s:OKState) => G_ZERO as nat, 
        ADD := (s:OKState) => G_VERYLOW, 
        MUL := (s:OKState) => G_LOW, 
        SUB := (s:OKState) => G_VERYLOW, 
        DIV := (s:OKState) => G_LOW, 
        SDIV := (s:OKState) => G_LOW, 
        MOD := (s:OKState) => G_LOW, 
        SMOD := (s:OKState) => G_LOW, 
        ADDMOD := (s:OKState) => G_MID, 
        MULMOD := (s:OKState) => G_MID, 
        // EXP := (s:OKState) => 1, 
        SIGNEXTEND := (s:OKState) => G_LOW, 
        // 0x10s: Comparison & Bitwise Logic
        LT := (s:OKState) => G_VERYLOW, 
        GT := (s:OKState) => G_VERYLOW, 
        SLT := (s:OKState) => G_VERYLOW, 
        SGT := (s:OKState) => G_VERYLOW, 
        EQ := (s:OKState) => G_VERYLOW, 
        ISZERO := (s:OKState) => G_VERYLOW, 
        AND := (s:OKState) => G_VERYLOW, 
        OR := (s:OKState) => G_VERYLOW, 
        XOR := (s:OKState) => G_VERYLOW, 
        NOT := (s:OKState) => G_VERYLOW, 
        BYTE := (s:OKState) => G_VERYLOW, 
        SHL := (s:OKState) => G_VERYLOW, 
        SHR := (s:OKState) => G_VERYLOW, 
        // SAR := (s:OKState) => 1, 
        // 0x20s
        //  KECCAK256 := (s:OKState) => 1, 
        // 0x30s: Environment Information
        ADDRESS := (s:OKState) => G_BASE, 
        BALANCE := (s:OKState) => G_BALANCE, 
        ORIGIN := (s:OKState) => G_BASE, 
        CALLER := (s:OKState) => G_BASE, 
        CALLVALUE := (s:OKState) => G_BASE, 
        CALLDATALOAD := (s:OKState) => G_VERYLOW, 
        // CALLDATASIZE := (s:OKState) => 1, 
        CALLDATACOPY := (s:OKState) => G_COPY, 
        // CODESIZE := (s:OKState) => 1, 
        CODECOPY := (s:OKState) => G_COPY, 
        GASPRICE := (s:OKState) => G_BASE, 
        // EXTCODESIZE := (s:OKState) => 1, 
        // EXTCODECOPY := (s:OKState) => 1, 
        RETURNDATASIZE := (s:OKState) => G_BASE, 
        RETURNDATACOPY := (s:OKState) => G_COPY, 
        //  EXTCODEHASH := (s:OKState) => 1, 
        // 0x40s: Block Information
        // BLOCKHASH := (s:OKState) => 1, 
        COINBASE := (s:OKState) => G_BASE, 
        TIMESTAMP := (s:OKState) => G_BASE, 
        NUMBER := (s:OKState) => G_BASE, 
        DIFFICULTY := (s:OKState) => G_BASE, 
        GASLIMIT := (s:OKState) => G_BASE, 
        //  CHAINID := (s:OKState) => 1, 
        //  SELFBALANCE := (s:OKState) => 1, 
        // 0x50s: Stack, Memory, Storage and Flow
        POP := (s:OKState) => G_BASE, 
        MLOAD := (s:OKState) => G_VERYLOW, 
        MSTORE := (s:OKState) => G_VERYLOW, 
        MSTORE8 := (s:OKState) => G_VERYLOW, 
        // SLOAD := (s:OKState) => 1, 
        // SSTORE := (s:OKState) => 1, 
        JUMP := (s:OKState) => G_MID, 
        // JUMPI := (s:OKState) => 1, 
        PC := (s:OKState) => G_BASE,
        JUMPDEST := (s:OKState) => G_HIGH, 
        // 0x60s & 0x70s: Push operations
        PUSH1 := (s: OKState) => G_VERYLOW,
        PUSH2 := (s:OKState) => G_VERYLOW,
        // PUSH3 := (s:OKState) => 1,
        // PUSH4 := (s:OKState) => 1,
        // PUSH5 := (s:OKState) => 1,
        // PUSH6 := (s:OKState) => 1,
        // PUSH7 := (s:OKState) => 1,
        // PUSH8 := (s:OKState) => 1,
        // PUSH9 := (s:OKState) => 1,
        // PUSH10 := (s:OKState) => 1,
        // PUSH11 := (s:OKState) => 1,
        // 0x80s: Duplicate operations
        DUP1 := (s:OKState) => G_VERYLOW, 
        DUP2 := (s:OKState) => G_VERYLOW, 
        DUP3 := (s:OKState) => G_VERYLOW, 
        DUP4 := (s:OKState) => G_VERYLOW, 
        DUP5 := (s:OKState) => G_VERYLOW, 
        DUP6 := (s:OKState) => G_VERYLOW, 
        DUP7 := (s:OKState) => G_VERYLOW, 
        DUP8 := (s:OKState) => G_VERYLOW, 
        DUP9 := (s:OKState) => G_VERYLOW, 
        DUP10 := (s:OKState) => G_VERYLOW, 
        DUP11 := (s:OKState) => G_VERYLOW, 
        DUP12 := (s:OKState) => G_VERYLOW, 
        DUP13 := (s:OKState) => G_VERYLOW, 
        DUP14 := (s:OKState) => G_VERYLOW, 
        DUP15 := (s:OKState) => G_VERYLOW, 
        DUP16 := (s:OKState) => G_VERYLOW, 
        // 0x90s: Exchange operations
        SWAP1 := (s:OKState) => G_VERYLOW, 
        SWAP2 := (s:OKState) => G_VERYLOW, 
        SWAP3 := (s:OKState) => G_VERYLOW, 
        SWAP4 := (s:OKState) => G_VERYLOW, 
        SWAP5 := (s:OKState) => G_VERYLOW, 
        SWAP6 := (s:OKState) => G_VERYLOW, 
        SWAP7 := (s:OKState) => G_VERYLOW, 
        SWAP8 := (s:OKState) => G_VERYLOW, 
        SWAP9 := (s:OKState) => G_VERYLOW, 
        SWAP10 := (s:OKState) => G_VERYLOW, 
        SWAP11 := (s:OKState) => G_VERYLOW, 
        SWAP12 := (s:OKState) => G_VERYLOW, 
        SWAP13 := (s:OKState) => G_VERYLOW, 
        SWAP14 := (s:OKState) => G_VERYLOW, 
        SWAP15 := (s:OKState) => G_VERYLOW, 
        SWAP16 := (s:OKState) => G_VERYLOW, 
        // 0xA0s: Log operations
        // else if LOG0 <=opcode <= LOG4 := (s:OKState)
        //   var k := opcode - LOG0) as int; evalLOG(st,k),
        // 0xf0
        // CREATE := (s:OKState) => 1, 
        // CALL := (s:OKState) => 1, 
        // CALLCODE := (s:OKState) => 1, 
        RETURN := (s:OKState) => G_ZERO, 
        // DELEGATECALL := (s:OKState) => 1, 
        // CREATE2 := (s:OKState) => 1, 
        // STATICCALL := (s:OKState) => 1, 
        REVERT := (s:OKState) => G_ZERO,
        SELFDESTRUCT := (s:OKState) => 1
    ]  
    
}

	