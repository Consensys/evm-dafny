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

	import opened Int
	import opened Opcode
	import opened EvmState

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
