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

include "./opcodes.dfy"
include "./state.dfy"
module Gas {
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

}

	