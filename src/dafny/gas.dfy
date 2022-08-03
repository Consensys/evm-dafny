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
include "util/ExtraTypes.dfy"
module Gas {

	import opened Opcode
	import opened EvmState
    import opened Int
    import ExtraTypes

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
        PUSH2 := (s: OKState) => 1,
        PUSH3 := (s: OKState) => 1,
        PUSH4 := (s: OKState) => 1,
        // PUSH5 := (s: OKState) => 1,
        // PUSH6 := (s: OKState) => 1,
        // PUSH7 := (s: OKState) => 1,
        // PUSH8 := (s: OKState) => 1,
        // PUSH9 := (s: OKState) => 1,
        // PUSH10 := (s: OKState) => 1,
        // PUSH11 := (s: OKState) => 1,
        // PUSH12 := (s: OKState) => 1,
        // PUSH13 := (s: OKState) => 1,
        // PUSH14 := (s: OKState) => 1,
        // PUSH15 := (s: OKState) => 1,
        // PUSH16 := (s: OKState) => 1,
        // PUSH17 := (s: OKState) => 1,
        // PUSH18 := (s: OKState) => 1,
        // PUSH19 := (s: OKState) => 1,
        // PUSH20 := (s: OKState) => 1,
        // PUSH21 := (s: OKState) => 1,
        // PUSH22 := (s: OKState) => 1,
        // PUSH23 := (s: OKState) => 1,
        // PUSH24 := (s: OKState) => 1,
        // PUSH25 := (s: OKState) => 1,
        // PUSH26 := (s: OKState) => 1,
        // PUSH27 := (s: OKState) => 1,
        // PUSH28 := (s: OKState) => 1,
        // PUSH29 := (s: OKState) => 1,
        // PUSH30 := (s: OKState) => 1,
        // PUSH31 := (s: OKState) => 1,
        // PUSH32 := (s: OKState) => 1,
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
        // SWAP10 := (s:OKState) => 1,
        // SWAP11 := (s:OKState) => 1,
        // SWAP12 := (s:OKState) => 1,
        // SWAP13 := (s:OKState) => 1,
        // SWAP14 := (s:OKState) => 1,
        // SWAP15 := (s:OKState) => 1,
        // SWAP16 := (s:OKState) => 1,
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

    /** The constant Gas cost for each  */
    function method GasOne(op: u8): ExtraTypes.Option<OKState -> nat> 
    {
        match op 
            case STOP => ExtraTypes.Some((s:OKState) => 1 as nat)
            case ADD => ExtraTypes.Some((s:OKState) => 1)
            case MUL => ExtraTypes.Some((s:OKState) => 1)
            case SUB => ExtraTypes.Some((s:OKState) => 1)
            case DIV => ExtraTypes.Some((s:OKState) => 1)
            case SDIV => ExtraTypes.Some((s:OKState) => 1)
            case MOD => ExtraTypes.Some((s:OKState) => 1)
            case SMOD => ExtraTypes.Some((s:OKState) => 1)
            case ADDMOD => ExtraTypes.Some((s:OKState) => 1)
            case MULMOD => ExtraTypes.Some((s:OKState) => 1)
            case EXP => ExtraTypes.Some((s:OKState) => 1)
            case SIGNEXTEND => ExtraTypes.Some((s:OKState) => 1)
            // 0x10s: Comparison & Bitwise Logic
            case LT => ExtraTypes.Some((s:OKState) => 1)
            case GT => ExtraTypes.Some((s:OKState) => 1)
            case SLT => ExtraTypes.Some((s:OKState) => 1)
            case SGT => ExtraTypes.Some((s:OKState) => 1)
            case EQ => ExtraTypes.Some((s:OKState) => 1)
            case ISZERO => ExtraTypes.Some((s:OKState) => 1)
            case AND => ExtraTypes.Some((s:OKState) => 1)
            case OR => ExtraTypes.Some((s:OKState) => 1)
            case XOR => ExtraTypes.Some((s:OKState) => 1)
            case NOT => ExtraTypes.Some((s:OKState) => 1)
            case BYTE => ExtraTypes.Some((s:OKState) => 1)
            case SHL => ExtraTypes.Some((s:OKState) => 1)
            case SHR => ExtraTypes.Some((s:OKState) => 1)
            case SAR => ExtraTypes.Some((s:OKState) => 1)
            // 0x20s
            //  KECCAK256 => ExtraTypes.Some((s:OKState) => 1)
            // 0x30s: Environment Information
            case ADDRESS => ExtraTypes.Some((s:OKState) => 1)
            case BALANCE => ExtraTypes.Some((s:OKState) => 1)
            case ORIGIN => ExtraTypes.Some((s:OKState) => 1)
            case CALLER => ExtraTypes.Some((s:OKState) => 1)
            case CALLVALUE => ExtraTypes.Some((s:OKState) => 1)
            case CALLDATALOAD => ExtraTypes.Some((s:OKState) => 1)
            case CALLDATASIZE => ExtraTypes.Some((s:OKState) => 1)
            case CALLDATACOPY => ExtraTypes.Some((s:OKState) => 1)
            case CODESIZE => ExtraTypes.Some((s:OKState) => 1)
            case CODECOPY => ExtraTypes.Some((s:OKState) => 1)
            case GASPRICE => ExtraTypes.Some((s:OKState) => 1)
            case EXTCODESIZE => ExtraTypes.Some((s:OKState) => 1)
            case EXTCODECOPY => ExtraTypes.Some((s:OKState) => 1)
            case RETURNDATASIZE => ExtraTypes.Some((s:OKState) => 1)
            case RETURNDATACOPY => ExtraTypes.Some((s:OKState) => 1)
            //  EXTCODEHASH => ExtraTypes.Some((s:OKState) => 1)
            // 0x40s: Block Information
            case BLOCKHASH => ExtraTypes.Some((s:OKState) => 1)
            case COINBASE => ExtraTypes.Some((s:OKState) => 1)
            case TIMESTAMP => ExtraTypes.Some((s:OKState) => 1)
            case NUMBER => ExtraTypes.Some((s:OKState) => 1)
            case DIFFICULTY => ExtraTypes.Some((s:OKState) => 1)
            case GASLIMIT => ExtraTypes.Some((s:OKState) => 1)
            //  CHAINID => ExtraTypes.Some((s:OKState) => 1)
            //  SELFBALANCE => ExtraTypes.Some((s:OKState) => 1)
            // 0x50s: Stack, Memory, Storage and Flow
            case POP => ExtraTypes.Some((s:OKState) => 1)
            case MLOAD => ExtraTypes.Some((s:OKState) => 1)
            case MSTORE => ExtraTypes.Some((s:OKState) => 1)
            case MSTORE8 => ExtraTypes.Some((s:OKState) => 1)
            case SLOAD => ExtraTypes.Some((s:OKState) => 1)
            case SSTORE => ExtraTypes.Some((s:OKState) => 1)
            case JUMP => ExtraTypes.Some((s:OKState) => 1)
            case JUMPI => ExtraTypes.Some((s:OKState) => 1)
            case PC => ExtraTypes.Some((s:OKState) => 1)
            case JUMPDEST => ExtraTypes.Some((s:OKState) => 1)
            // 0x60s & 0x70s: Push operations
            case PUSH1 => ExtraTypes.Some((s: OKState) => 1)
            case PUSH2 => ExtraTypes.Some((s: OKState) => 1)
            case PUSH3 => ExtraTypes.Some((s: OKState) => 1)
            case PUSH4 => ExtraTypes.Some((s: OKState) => 1)
            // PUSH5 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH6 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH7 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH8 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH9 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH10 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH11 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH12 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH13 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH14 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH15 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH16 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH17 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH18 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH19 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH20 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH21 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH22 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH23 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH24 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH25 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH26 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH27 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH28 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH29 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH30 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH31 => ExtraTypes.Some((s: OKState) => 1)
            case  PUSH32 => ExtraTypes.Some((s: OKState) => 1)
            // 0x80s: Duplicate operations
            case DUP1 => ExtraTypes.Some((s:OKState) => 1)
            case DUP2 => ExtraTypes.Some((s:OKState) => 1)
            case DUP3 => ExtraTypes.Some((s:OKState) => 1)
            case DUP4 => ExtraTypes.Some((s:OKState) => 1)
            case DUP5 => ExtraTypes.Some((s:OKState) => 1)
            case DUP6 => ExtraTypes.Some((s:OKState) => 1)
            case DUP7 => ExtraTypes.Some((s:OKState) => 1)
            case DUP8 => ExtraTypes.Some((s:OKState) => 1)
            case DUP9 => ExtraTypes.Some((s:OKState) => 1)
            case DUP10 => ExtraTypes.Some((s:OKState) => 1)
            case DUP11 => ExtraTypes.Some((s:OKState) => 1)
            case DUP12 => ExtraTypes.Some((s:OKState) => 1)
            case DUP13 => ExtraTypes.Some((s:OKState) => 1)
            case DUP14 => ExtraTypes.Some((s:OKState) => 1)
            case DUP15 => ExtraTypes.Some((s:OKState) => 1)
            case DUP16 => ExtraTypes.Some((s:OKState) => 1)
            // 0x90s: Exchange operations
            case SWAP1 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP2 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP3 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP4 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP5 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP6 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP7 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP8 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP9 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP10 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP11 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP12 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP13 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP14 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP15 => ExtraTypes.Some((s:OKState) => 1)
            case SWAP16 => ExtraTypes.Some((s:OKState) => 1)
            // 0xA0s: Log operations
            // else if LOG0 <=opcode <= LOG4 => (s:OKState
            //   var k => opcode - LOG0) as int; evalLOG(st,k)
            // 0xf0
            case CREATE => ExtraTypes.Some((s:OKState) => 1)
            case CALL => ExtraTypes.Some((s:OKState) => 1)
            case CALLCODE => ExtraTypes.Some((s:OKState) => 1)
            case RETURN => ExtraTypes.Some((s:OKState) => 1)
            case DELEGATECALL => ExtraTypes.Some((s:OKState) => 1)
            // case CREATE2 => ExtraTypes.Some((s:OKState) => 1)
            case STATICCALL => ExtraTypes.Some((s:OKState) => 1)
            case REVERT => ExtraTypes.Some((s:OKState) => 1)
            case SELFDESTRUCT => ExtraTypes.Some((s:OKState) => 1)
            case _ =>  ExtraTypes.None
    } 

   

}
