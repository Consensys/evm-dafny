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

    /* this is an implementation of the constant parts of the gas cost function C in YP (see H.1 page 29, BERLIN VERSION 3078285 – 2022-07-13) */
    function method gasCostConstants(opcode: u8, vm: State): nat
        {
            match vm
                case OK(evm) =>
                    (match opcode
                        case STOP => G_zero 
                        case RETURN => G_zero 
                        case REVERT => G_zero 
                        case ADDRESS => G_base 
                        case ORIGIN => G_base 
                        case CALLER => G_base 
                        case CALLVALUE => G_base 
                        case CALLDATASIZE => G_base 
                        case CODESIZE => G_base 
                        case GASPRICE => G_base 
                        case COINBASE => G_base 
                        case TIMESTAMP => G_base 
                        case NUMBER => G_base 
                        case DIFFICULTY => G_base 
                        case GASLIMIT => G_base 
                        case RETURNDATASIZE => G_base 
                        case POP => G_base 
                        case PC => G_base
                        case MSIZE => G_base 
                        case GAS => G_base 
                        case CALLDATALOAD => G_verylow 
                        case MLOAD => G_verylow 
                        case MSTORE => G_verylow 
                        case MSTORE8 => G_verylow 
                        case PUSH1 => G_verylow
                        case PUSH2 => G_verylow 
                        case PUSH3 => G_verylow
                        case PUSH4 => G_verylow
                        case PUSH5 => G_verylow
                        case PUSH6 => G_verylow
                        case PUSH7 => G_verylow 
                        case PUSH8 => G_verylow 
                        case PUSH9 => G_verylow 
                        case PUSH10 => G_verylow
                        case PUSH11 => G_verylow
                        case PUSH12 => G_verylow 
                        case PUSH13 => G_verylow 
                        case PUSH14 => G_verylow 
                        case PUSH15 => G_verylow 
                        case PUSH16 => G_verylow
                        case PUSH17 => G_verylow
                        case PUSH18 => G_verylow
                        case PUSH19 => G_verylow
                        case PUSH20 => G_verylow 
                        case PUSH21 => G_verylow 
                        case PUSH22 => G_verylow 
                        case PUSH23 => G_verylow
                        case PUSH24 => G_verylow
                        case PUSH25 => G_verylow 
                        case PUSH26 => G_verylow 
                        case PUSH27 => G_verylow
                        case PUSH28 => G_verylow 
                        case PUSH29 => G_verylow 
                        case PUSH30 => G_verylow
                        case PUSH31 => G_verylow
                        case PUSH32 => G_verylow 
                        case DUP1 => G_verylow 
                        case DUP2 => G_verylow
                        case DUP3 => G_verylow
                        case DUP4 => G_verylow
                        case DUP5 => G_verylow
                        case DUP6 => G_verylow 
                        case DUP7 => G_verylow 
                        case DUP8 => G_verylow 
                        case DUP9 => G_verylow
                        case DUP10 => G_verylow
                        case DUP11 => G_verylow 
                        case DUP12 => G_verylow 
                        case DUP13 => G_verylow
                        case DUP14 => G_verylow 
                        case DUP15 => G_verylow 
                        case DUP16 => G_verylow
                        case SWAP1 => G_verylow 
                        case SWAP2 => G_verylow
                        case SWAP3 => G_verylow
                        case SWAP4 => G_verylow
                        case SWAP5 => G_verylow
                        case SWAP6 => G_verylow 
                        case SWAP7 => G_verylow 
                        case SWAP8 => G_verylow 
                        case SWAP9 => G_verylow
                        case SWAP10 => G_verylow
                        case SWAP11 => G_verylow 
                        case SWAP12 => G_verylow 
                        case SWAP13 => G_verylow
                        case SWAP14 => G_verylow 
                        case SWAP15 => G_verylow 
                        case SWAP16 => G_verylow
                        case ADD => G_verylow 
                        case SUB => G_verylow
                        case LT => G_verylow
                        case GT => G_verylow
                        case SLT => G_verylow
                        case SGT => G_verylow
                        case EQ => G_verylow
                        case ISZERO => G_verylow
                        case AND => G_verylow
                        case OR => G_verylow
                        case XOR => G_verylow
                        case BYTE => G_verylow
                        case SHL => G_verylow
                        case SHR => G_verylow                
                        case MUL => G_low
                        case DIV => G_low
                        case SDIV => G_low
                        case MOD => G_low
                        case SMOD => G_low
                        case SIGNEXTEND => G_low
                        case ADDMOD => G_mid
                        case MULMOD => G_mid
                        case JUMP => G_mid
                        case JUMPDEST => G_high
                        case CALLDATACOPY => G_copy
                        case CODECOPY => G_copy
                        case RETURNDATACOPY => G_copy
                        case BALANCE => G_balance
                        case EXTCODECOPY => G_extcode
                        // given we are not dealing with call or storage, I am setting them all to zero for now
                        case _ => 0)
                case RETURNS(_,_) => 0
                case REVERTS(_,_) => 0
                case _ => 0
        } 

/** The constant Gas cost for each opcode. */ 
    const GAS_ONE := map[   
        STOP := (s:OKState) => gasCostConstants(STOP, s), 
        ADD := (s:OKState) => gasCostConstants(ADD, s), 
        MUL := (s:OKState) => gasCostConstants(MUL, s), 
        SUB := (s:OKState) => gasCostConstants(SUB, s), 
        DIV := (s:OKState) => gasCostConstants(DIV, s), 
        SDIV := (s:OKState) => gasCostConstants(SDIV, s), 
        MOD := (s:OKState) => gasCostConstants(MOD, s), 
        SMOD := (s:OKState) => gasCostConstants(SMOD, s), 
        ADDMOD := (s:OKState) => gasCostConstants(ADDMOD, s), 
        MULMOD := (s:OKState) => gasCostConstants(MULMOD, s), 
        LT := (s:OKState) => gasCostConstants(LT, s), 
        GT := (s:OKState) => gasCostConstants(GT, s), 
        SLT := (s:OKState) => gasCostConstants(SLT, s), 
        SGT := (s:OKState) => gasCostConstants(SGT, s), 
        EQ := (s:OKState) => gasCostConstants(EQ, s), 
        ISZERO := (s:OKState) => gasCostConstants(ISZERO, s), 
        AND := (s:OKState) => gasCostConstants(AND, s), 
        OR := (s:OKState) => gasCostConstants(OR, s), 
        XOR := (s:OKState) => gasCostConstants(XOR, s), 
        NOT := (s:OKState) => gasCostConstants(NOT, s), 
        BYTE := (s:OKState) => gasCostConstants(BYTE, s), 
        SHL := (s:OKState) => gasCostConstants(SHL, s), 
        SHR := (s:OKState) => gasCostConstants(SHR, s), 
        CALLDATALOAD := (s:OKState) => gasCostConstants(CALLDATALOAD, s), 
        CALLDATASIZE := (s:OKState) => gasCostConstants(CALLDATASIZE, s), 
        CALLDATACOPY := (s:OKState) => gasCostConstants(CALLDATACOPY, s), 
        CODESIZE := (s:OKState) => gasCostConstants(CODESIZE, s), 
        CODECOPY := (s:OKState) => gasCostConstants(CODECOPY, s), 
        GASPRICE := (s:OKState) => gasCostConstants(GASPRICE, s), 
        EXTCODESIZE := (s:OKState) => gasCostConstants(EXTCODESIZE, s), 
        EXTCODECOPY := (s:OKState) => gasCostConstants(EXTCODECOPY, s), 
        RETURNDATASIZE := (s:OKState) => gasCostConstants(RETURNDATASIZE, s), 
        RETURNDATACOPY := (s:OKState) => gasCostConstants(RETURNDATACOPY, s), 
        BLOCKHASH := (s:OKState) => gasCostConstants(BLOCKHASH, s), 
        COINBASE := (s:OKState) => gasCostConstants(COINBASE, s), 
        TIMESTAMP := (s:OKState) => gasCostConstants(TIMESTAMP, s), 
        NUMBER := (s:OKState) => gasCostConstants(NUMBER, s), 
        DIFFICULTY := (s:OKState) => gasCostConstants(DIFFICULTY, s), 
        GASLIMIT := (s:OKState) => gasCostConstants(GASLIMIT, s), 
        POP := (s:OKState) => gasCostConstants(POP, s), 
        MLOAD := (s:OKState) => gasCostConstants(MLOAD, s), 
        MSTORE := (s:OKState) => gasCostConstants(MSTORE, s), 
        MSTORE8 := (s:OKState) => gasCostConstants(MSTORE8, s), 
        SLOAD := (s:OKState) => gasCostConstants(SLOAD, s), 
        SSTORE := (s:OKState) => gasCostConstants(SSTORE, s), 
        JUMP := (s:OKState) => gasCostConstants(JUMP, s), 
        JUMPI := (s:OKState) => gasCostConstants(JUMPI, s), 
        PC := (s:OKState) => gasCostConstants(PC, s),
        JUMPDEST := (s:OKState) => gasCostConstants(JUMPDEST, s), 
        PUSH1 := (s: OKState) => gasCostConstants(PUSH1, s),
        PUSH2 := (s:OKState) => gasCostConstants(PUSH2, s),
        PUSH3 := (s: OKState) => gasCostConstants(PUSH3, s),
        PUSH4 := (s:OKState) => gasCostConstants(PUSH4, s),
        PUSH5 := (s: OKState) => gasCostConstants(PUSH5, s),
        PUSH6 := (s:OKState) => gasCostConstants(PUSH6, s),
        PUSH7 := (s: OKState) => gasCostConstants(PUSH7, s),
        PUSH8 := (s:OKState) => gasCostConstants(PUSH8, s),
        PUSH9 := (s: OKState) => gasCostConstants(PUSH9, s),
        PUSH10 := (s:OKState) => gasCostConstants(PUSH10, s),
        PUSH11 := (s: OKState) => gasCostConstants(PUSH11, s),
        PUSH12 := (s:OKState) => gasCostConstants(PUSH12, s),
        PUSH13 := (s: OKState) => gasCostConstants(PUSH13, s),
        PUSH14 := (s:OKState) => gasCostConstants(PUSH14, s),
        PUSH15 := (s: OKState) => gasCostConstants(PUSH15, s),
        PUSH16 := (s:OKState) => gasCostConstants(PUSH16, s),
        PUSH17 := (s: OKState) => gasCostConstants(PUSH17, s),
        PUSH18 := (s:OKState) => gasCostConstants(PUSH18, s),
        PUSH19 := (s: OKState) => gasCostConstants(PUSH19, s),
        PUSH20 := (s:OKState) => gasCostConstants(PUSH20, s),
        PUSH21 := (s: OKState) => gasCostConstants(PUSH21, s),
        PUSH22 := (s:OKState) => gasCostConstants(PUSH22, s),
        PUSH23 := (s: OKState) => gasCostConstants(PUSH23, s),
        PUSH24 := (s:OKState) => gasCostConstants(PUSH24, s),
        PUSH25 := (s: OKState) => gasCostConstants(PUSH25, s),
        PUSH26 := (s:OKState) => gasCostConstants(PUSH26, s),
        PUSH27 := (s: OKState) => gasCostConstants(PUSH27, s),
        PUSH28 := (s:OKState) => gasCostConstants(PUSH28, s),
        PUSH29 := (s: OKState) => gasCostConstants(PUSH29, s),
        PUSH30 := (s:OKState) => gasCostConstants(PUSH30, s),
        PUSH31 := (s: OKState) => gasCostConstants(PUSH31, s),
        PUSH32 := (s:OKState) => gasCostConstants(PUSH32, s),
        DUP1 := (s:OKState) => gasCostConstants(DUP1, s), 
        DUP2 := (s:OKState) => gasCostConstants(DUP2, s), 
        DUP3 := (s:OKState) => gasCostConstants(DUP3, s), 
        DUP4 := (s:OKState) => gasCostConstants(DUP4, s), 
        DUP5 := (s:OKState) => gasCostConstants(DUP5, s), 
        DUP6 := (s:OKState) => gasCostConstants(DUP6, s), 
        DUP7 := (s:OKState) => gasCostConstants(DUP7, s), 
        DUP8 := (s:OKState) => gasCostConstants(DUP8, s), 
        DUP9 := (s:OKState) => gasCostConstants(DUP9, s), 
        DUP10 := (s:OKState) => gasCostConstants(DUP10, s), 
        DUP11 := (s:OKState) => gasCostConstants(DUP11, s), 
        DUP12 := (s:OKState) => gasCostConstants(DUP12, s), 
        DUP13 := (s:OKState) => gasCostConstants(DUP13, s), 
        DUP14 := (s:OKState) => gasCostConstants(DUP14, s), 
        DUP15 := (s:OKState) => gasCostConstants(DUP15, s), 
        DUP16 := (s:OKState) => gasCostConstants(DUP16, s), 
        SWAP1 := (s:OKState) => gasCostConstants(SWAP1, s), 
        SWAP2 := (s:OKState) => gasCostConstants(SWAP2, s), 
        SWAP3 := (s:OKState) => gasCostConstants(SWAP3, s), 
        SWAP4 := (s:OKState) => gasCostConstants(SWAP4, s), 
        SWAP5 := (s:OKState) => gasCostConstants(SWAP5, s), 
        SWAP6 := (s:OKState) => gasCostConstants(SWAP6, s), 
        SWAP7 := (s:OKState) => gasCostConstants(SWAP7, s), 
        SWAP8 := (s:OKState) => gasCostConstants(SWAP8, s), 
        SWAP9 := (s:OKState) => gasCostConstants(SWAP9, s), 
        SWAP10 := (s:OKState) => gasCostConstants(SWAP10, s), 
        SWAP11 := (s:OKState) => gasCostConstants(SWAP11, s), 
        SWAP12 := (s:OKState) => gasCostConstants(SWAP12, s), 
        SWAP13 := (s:OKState) => gasCostConstants(SWAP13, s), 
        SWAP14 := (s:OKState) => gasCostConstants(SWAP14, s), 
        SWAP15 := (s:OKState) => gasCostConstants(SWAP15, s), 
        SWAP16 := (s:OKState) => gasCostConstants(SWAP16, s), 
        RETURN := (s:OKState) => gasCostConstants(RETURN, s), 
        REVERT := (s:OKState) => gasCostConstants(REVERT, s),
        SELFDESTRUCT := (s:OKState) => gasCostConstants(SELFDESTRUCT, s) 
    ]  


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

	function method gasCost_alt(opcode: u8, vm: State): nat
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

	