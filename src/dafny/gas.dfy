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
	
	/** The constant Gas cost for each opcode. */ 
    const GAS_ONE := map[   
        Opcode.STOP := (s:OKState) => 1 as nat, 
        Opcode.ADD := (s:OKState) => 1, 
        Opcode.MUL := (s:OKState) => 1, 
        Opcode.SUB := (s:OKState) => 1, 
        Opcode.DIV := (s:OKState) => 1, 
        Opcode.SDIV := (s:OKState) => 1, 
        Opcode.MOD := (s:OKState) => 1, 
        Opcode.SMOD := (s:OKState) => 1, 
        Opcode.ADDMOD := (s:OKState) => 1, 
        Opcode.MULMOD := (s:OKState) => 1, 
        //  EXP := (s:OKState) => 1, 
        //  SIGNEXTEND := (s:OKState) => 1, 
        // 0x10s: Comparison & Bitwise Logic
        Opcode.LT := (s:OKState) => 1, 
        Opcode.GT := (s:OKState) => 1, 
        Opcode.SLT := (s:OKState) => 1, 
        Opcode.SGT := (s:OKState) => 1, 
        Opcode.EQ := (s:OKState) => 1, 
        Opcode.ISZERO := (s:OKState) => 1, 
        Opcode.AND := (s:OKState) => 1, 
        Opcode.OR := (s:OKState) => 1, 
        Opcode.XOR := (s:OKState) => 1, 
        Opcode.NOT := (s:OKState) => 1, 
        Opcode.BYTE := (s:OKState) => 1, 
        Opcode.SHL := (s:OKState) => 1, 
        Opcode.SHR := (s:OKState) => 1, 
        //  SAR := (s:OKState) => 1, 
        // 0x20s
        //  KECCAK256 := (s:OKState) => 1, 
        // 0x30s: Environment Information
        //  ADDRESS := (s:OKState) => 1, 
        //  BALANCE := (s:OKState) => 1, 
        //  ORIGIN := (s:OKState) => 1, 
        //  CALLER := (s:OKState) => 1, 
        //  CALLVALUE := (s:OKState) => 1, 
        Opcode.CALLDATALOAD := (s:OKState) => 1, 
        Opcode.CALLDATASIZE := (s:OKState) => 1, 
        Opcode.CALLDATACOPY := (s:OKState) => 1, 
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
        Opcode.POP := (s:OKState) => 1, 
        Opcode.MLOAD := (s:OKState) => 1, 
        Opcode.MSTORE := (s:OKState) => 1, 
        Opcode.MSTORE8 := (s:OKState) => 1, 
        Opcode.SLOAD := (s:OKState) => 1, 
        Opcode.SSTORE := (s:OKState) => 1, 
        Opcode.JUMP := (s:OKState) => 1, 
        Opcode.JUMPI := (s:OKState) => 1, 
        Opcode.PC := (s:OKState) => 1,
        Opcode.JUMPDEST := (s:OKState) => 1, 
        // 0x60s & 0x70s: Push operations
        Opcode.PUSH1 := (s: OKState) => 1,
        Opcode.PUSH2 := (s:OKState) => 1,
        // 0x80s: Duplicate operations
        Opcode.DUP1 := (s:OKState) => 1, 
        Opcode.DUP2 := (s:OKState) => 1, 
        Opcode.DUP3 := (s:OKState) => 1, 
        Opcode.DUP4 := (s:OKState) => 1, 
        Opcode.DUP5 := (s:OKState) => 1, 
        Opcode.DUP6 := (s:OKState) => 1, 
        Opcode.DUP7 := (s:OKState) => 1, 
        Opcode.DUP8 := (s:OKState) => 1, 
        Opcode.DUP9 := (s:OKState) => 1, 
        Opcode.DUP10 := (s:OKState) => 1, 
        Opcode.DUP11 := (s:OKState) => 1, 
        Opcode.DUP12 := (s:OKState) => 1, 
        Opcode.DUP13 := (s:OKState) => 1, 
        Opcode.DUP14 := (s:OKState) => 1, 
        Opcode.DUP15 := (s:OKState) => 1, 
        Opcode.DUP16 := (s:OKState) => 1, 
        // 0x90s: Exchange operations
        Opcode.SWAP1 := (s:OKState) => 1, 
        Opcode.SWAP2 := (s:OKState) => 1, 
        Opcode.SWAP3 := (s:OKState) => 1, 
        Opcode.SWAP4 := (s:OKState) => 1, 
        Opcode.SWAP5 := (s:OKState) => 1, 
        Opcode.SWAP6 := (s:OKState) => 1, 
        Opcode.SWAP7 := (s:OKState) => 1, 
        Opcode.SWAP8 := (s:OKState) => 1, 
        Opcode.SWAP9 := (s:OKState) => 1, 
        Opcode.SWAP10 := (s:OKState) => 1, 
        Opcode.SWAP11 := (s:OKState) => 1, 
        Opcode.SWAP12 := (s:OKState) => 1, 
        Opcode.SWAP13 := (s:OKState) => 1, 
        Opcode.SWAP14 := (s:OKState) => 1, 
        Opcode.SWAP15 := (s:OKState) => 1, 
        Opcode.SWAP16 := (s:OKState) => 1, 
        // 0xA0s: Log operations
        // else if LOG0 <=opcode <= LOG4 := (s:OKState)
         //   var k := opcode - LOG0) as int; evalLOG(st,k),
        // 0xf0
        //  CREATE := (s:OKState) => 1, 
        //  CALL := (s:OKState) => 1, 
        //  CALLCODE := (s:OKState) => 1, 
        Opcode.RETURN := (s:OKState) => 1, 
        // DELEGATECALL := (s:OKState) => 1, 
        // CREATE2 := (s:OKState) => 1, 
        // STATICCALL := (s:OKState) => 1, 
        Opcode.REVERT := (s:OKState) => 1
        // SELFDESTRUCT := (s:OKState) => 1, 
    ]  

	import opened Int

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

	