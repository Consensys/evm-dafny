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

	
	/** The constant Gas cost for each opcode. */ 
    const GAS_ONE := map[   
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
        //  EXP := (s:OKState) => 1, 
        //  SIGNEXTEND := (s:OKState) => 1, 
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
        //  SAR := (s:OKState) => 1, 
        // 0x20s
        //  KECCAK256 := (s:OKState) => 1, 
        // 0x30s: Environment Information
        //  ADDRESS := (s:OKState) => 1, 
        //  BALANCE := (s:OKState) => 1, 
        //  ORIGIN := (s:OKState) => 1, 
        //  CALLER := (s:OKState) => 1, 
        //  CALLVALUE := (s:OKState) => 1, 
        CALLDATALOAD := (s:OKState) => 1, 
        CALLDATASIZE := (s:OKState) => 1, 
        CALLDATACOPY := (s:OKState) => 1, 
        //  CODESIZE := (s:OKState) => 1, 
        //  CODECOPY := (s:OKState) => 1, 
        //  GASPRICE := (s:OKState) => 1, 
        //  EXTCODESIZE := (s:OKState) => 1, 
        //  EXTCODECOPY := (s:OKState) => 1, 
        //  RETURNDATASIZE := (s:OKState) => 1, 
        //  RETURNDATACOPY := (s:OKState) => 1, 
        //  EXTCODEHASH := (s:OKState) => 1, 
        // 0x40s: Block Information
        //  BLOCKHASH := (s:OKState) => 1, 
        //  COINBASE := (s:OKState) => 1, 
        //  TIMESTAMP := (s:OKState) => 1, 
        //  NUMBER := (s:OKState) => 1, 
        //  DIFFICULTY := (s:OKState) => 1, 
        //  GASLIMIT := (s:OKState) => 1, 
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
        //  CREATE := (s:OKState) => 1, 
        //  CALL := (s:OKState) => 1, 
        //  CALLCODE := (s:OKState) => 1, 
        RETURN := (s:OKState) => 1, 
        // DELEGATECALL := (s:OKState) => 1, 
        // CREATE2 := (s:OKState) => 1, 
        // STATICCALL := (s:OKState) => 1, 
        REVERT := (s:OKState) => 1
        // SELFDESTRUCT := (s:OKState) => 1, 
    ]  

    const G_zero: nat := 0;
	const G_base: nat := 2;
	const G_verylow: nat := 3;
	const G_low: nat := 5;
	const G_mid: nat := 8;
	const G_high: nat := 10;
	const G_extcode: nat := 700;
	const G_balance: nat := 400;
	const G_sload: nat := 200;
	const G_jumpdest: nat := 1;
	const G_sset: nat := 20000;
	const G_sreset: nat := 5000;
	const R_sclear: nat := 15000;
	const R_selfdestruct: nat := 24000;
	const G_selfdestruct: nat := 5000;
	const G_create: nat := 32000;
	const G_codedeposit: nat := 200;
	const G_call: nat := 700;
	const G_callvalue: nat := 9000;
	const G_callstipend: nat := 2300;
	const G_newaccount: nat := 25000;
	const G_exp: nat := 10;
	const G_expbyte: nat := 50;
	const G_memory: nat := 3;
	const G_txcreate: nat := 32000;
	const G_txdatazero: nat := 4;
	const G_txdatanonzero: nat := 68;
	const G_transaction: nat := 21000;
	const G_log: nat := 375;
	const G_logdata: nat := 8;
	const G_logtopic: nat := 375;
	const G_sha3: nat := 30;
	const G_sha3word: nat := 6;
	const G_copy: nat := 3;
	const G_blockhash: nat := 20;
	const G_quaddivisor: nat := 100;


    const W_zero: seq<u8> := [STOP, RETURN, REVERT];
    const W_base: seq<u8> := [ADDRESS, ORIGIN, CALLER, CALLVALUE, CALLDATASIZE, CODESIZE, GASPRICE, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT,
                              RETURNDATASIZE, POP, PC, MSIZE, GAS]
    const W_verylow: seq<u8> := [CALLDATALOAD, MLOAD, MSTORE, MSTORE8, PUSH1, PUSH2, PUSH3, PUSH4, PUSH5, PUSH6,PUSH7, PUSH8, PUSH9, PUSH10, PUSH11, 
                                 PUSH12, PUSH13, PUSH14, PUSH15, PUSH16, PUSH17, PUSH18, PUSH19, PUSH20, PUSH21, PUSH22, PUSH23, PUSH24, PUSH25, PUSH26, 
                                 PUSH27, PUSH28, PUSH29, PUSH30, PUSH31, PUSH32, DUP1, DUP2, DUP3, DUP4, DUP5, DUP6, DUP7, DUP8, DUP9, DUP10, DUP11, 
                                 DUP12, DUP13, DUP4, DUP15, DUP16, SWAP1, SWAP2, SWAP3, SWAP4, SWAP5, SWAP6, SWAP7, SWAP8, SWAP9, SWAP10, SWAP11, 
                                 SWAP12, SWAP13, SWAP14, SWAP15, SWAP16,
                                 ADD, SUB, NOT, LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, BYTE, SHL, SHR, SAR]
    const W_low: seq<u8> := [MUL, DIV, SDIV, MOD, SMOD, SIGNEXTEND]
    const W_mid: seq<u8> := [ADDMOD, MULMOD, JUMP]
    const W_high: seq<u8> := [JUMPI]
    const W_copy: seq<u8> := [CALLDATACOPY, CODECOPY, RETURNDATACOPY]
    const W_call: seq<u8> := [CALL, CALLCODE, DELEGATECALL, STATICCALL]
    const W_extaccount: seq<u8> := [BALANCE, EXTCODESIZE]

	function method gasCost(opcode: u8, vm: State): nat
		{
			match vm 
				case OK(evm) => 
					if opcode in W_zero
						then G_zero
					else if opcode in W_base 
						then G_base
					else if opcode in W_verylow
						then G_verylow
					else if opcode in W_low
						then G_low
					else if opcode in W_mid
						then G_mid
					else if opcode in W_high
						then G_high
					else if opcode in W_copy
						then G_copy
					else if opcode == JUMPDEST
						then G_jumpdest
					else
						0
				case RETURNS(_,_) =>
					0
				case REVERTS(_,_) =>
					0
				case _ => 
					0
		}
}

	