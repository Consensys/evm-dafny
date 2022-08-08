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
    import opened ExtraTypes 

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
    function method GasOne(op: u8): Option<OKState -> nat> 
    {
        match op 
            case STOP => Some((s:OKState) => 1 as nat)
            case ADD => Some((s:OKState) => 1)
            case MUL => Some((s:OKState) => 1)
            case SUB => Some((s:OKState) => 1)
            case DIV => Some((s:OKState) => 1)
            case SDIV => Some((s:OKState) => 1)
            case MOD => Some((s:OKState) => 1)
            case SMOD => Some((s:OKState) => 1)
            case ADDMOD => Some((s:OKState) => 1)
            case MULMOD => Some((s:OKState) => 1)
            case EXP => Some((s:OKState) => 1)
            case SIGNEXTEND => Some((s:OKState) => 1)
            // 0x10s: Comparison & Bitwise Logic
            case LT => Some((s:OKState) => 1)
            case GT => Some((s:OKState) => 1)
            case SLT => Some((s:OKState) => 1)
            case SGT => Some((s:OKState) => 1)
            case EQ => Some((s:OKState) => 1)
            case ISZERO => Some((s:OKState) => 1)
            case AND => Some((s:OKState) => 1)
            case OR => Some((s:OKState) => 1)
            case XOR => Some((s:OKState) => 1)
            case NOT => Some((s:OKState) => 1)
            case BYTE => Some((s:OKState) => 1)
            case SHL => Some((s:OKState) => 1)
            case SHR => Some((s:OKState) => 1)
            case SAR => Some((s:OKState) => 1)
            // 0x20s
            //  KECCAK256 => Some((s:OKState) => 1)
            // 0x30s: Environment Information
            case ADDRESS => Some((s:OKState) => 1)
            case BALANCE => Some((s:OKState) => 1)
            case ORIGIN => Some((s:OKState) => 1)
            case CALLER => Some((s:OKState) => 1)
            case CALLVALUE => Some((s:OKState) => 1)
            case CALLDATALOAD => Some((s:OKState) => 1)
            case CALLDATASIZE => Some((s:OKState) => 1)
            case CALLDATACOPY => Some((s:OKState) => 1)
            case CODESIZE => Some((s:OKState) => 1)
            case CODECOPY => Some((s:OKState) => 1)
            case GASPRICE => Some((s:OKState) => 1)
            case EXTCODESIZE => Some((s:OKState) => 1)
            case EXTCODECOPY => Some((s:OKState) => 1)
            case RETURNDATASIZE => Some((s:OKState) => 1)
            case RETURNDATACOPY => Some((s:OKState) => 1)
            //  EXTCODEHASH => Some((s:OKState) => 1)
            // 0x40s: Block Information
            case BLOCKHASH => Some((s:OKState) => 1)
            case COINBASE => Some((s:OKState) => 1)
            case TIMESTAMP => Some((s:OKState) => 1)
            case NUMBER => Some((s:OKState) => 1)
            case DIFFICULTY => Some((s:OKState) => 1)
            case GASLIMIT => Some((s:OKState) => 1)
            //  CHAINID => Some((s:OKState) => 1)
            //  SELFBALANCE => Some((s:OKState) => 1)
            // 0x50s: Stack, Memory, Storage and Flow
            case POP => Some((s:OKState) => 1)
            case MLOAD => Some((s:OKState) => 1)
            case MSTORE => Some((s:OKState) => 1)
            case MSTORE8 => Some((s:OKState) => 1)
            case SLOAD => Some((s:OKState) => 1)
            case SSTORE => Some((s:OKState) => 1)
            case JUMP => Some((s:OKState) => 1)
            case JUMPI => Some((s:OKState) => 1)
            case PC => Some((s:OKState) => 1)
            case MSIZE => Some((s:OKState) => 1)
            case JUMPDEST => Some((s:OKState) => 1)
            // 0x60s & 0x70s: Push operations
            case PUSH1 => Some((s: OKState) => 1)
            case PUSH2 => Some((s: OKState) => 1)
            case PUSH3 => Some((s: OKState) => 1)
            case PUSH4 => Some((s: OKState) => 1)
            // PUSH5 => Some((s: OKState) => 1)
            case  PUSH6 => Some((s: OKState) => 1)
            case  PUSH7 => Some((s: OKState) => 1)
            case  PUSH8 => Some((s: OKState) => 1)
            case  PUSH9 => Some((s: OKState) => 1)
            case  PUSH10 => Some((s: OKState) => 1)
            case  PUSH11 => Some((s: OKState) => 1)
            case  PUSH12 => Some((s: OKState) => 1)
            case  PUSH13 => Some((s: OKState) => 1)
            case  PUSH14 => Some((s: OKState) => 1)
            case  PUSH15 => Some((s: OKState) => 1)
            case  PUSH16 => Some((s: OKState) => 1)
            case  PUSH17 => Some((s: OKState) => 1)
            case  PUSH18 => Some((s: OKState) => 1)
            case  PUSH19 => Some((s: OKState) => 1)
            case  PUSH20 => Some((s: OKState) => 1)
            case  PUSH21 => Some((s: OKState) => 1)
            case  PUSH22 => Some((s: OKState) => 1)
            case  PUSH23 => Some((s: OKState) => 1)
            case  PUSH24 => Some((s: OKState) => 1)
            case  PUSH25 => Some((s: OKState) => 1)
            case  PUSH26 => Some((s: OKState) => 1)
            case  PUSH27 => Some((s: OKState) => 1)
            case  PUSH28 => Some((s: OKState) => 1)
            case  PUSH29 => Some((s: OKState) => 1)
            case  PUSH30 => Some((s: OKState) => 1)
            case  PUSH31 => Some((s: OKState) => 1)
            case  PUSH32 => Some((s: OKState) => 1)
            // 0x80s: Duplicate operations
            case DUP1 => Some((s:OKState) => 1)
            case DUP2 => Some((s:OKState) => 1)
            case DUP3 => Some((s:OKState) => 1)
            case DUP4 => Some((s:OKState) => 1)
            case DUP5 => Some((s:OKState) => 1)
            case DUP6 => Some((s:OKState) => 1)
            case DUP7 => Some((s:OKState) => 1)
            case DUP8 => Some((s:OKState) => 1)
            case DUP9 => Some((s:OKState) => 1)
            case DUP10 => Some((s:OKState) => 1)
            case DUP11 => Some((s:OKState) => 1)
            case DUP12 => Some((s:OKState) => 1)
            case DUP13 => Some((s:OKState) => 1)
            case DUP14 => Some((s:OKState) => 1)
            case DUP15 => Some((s:OKState) => 1)
            case DUP16 => Some((s:OKState) => 1)
            // 0x90s: Exchange operations
            case SWAP1 => Some((s:OKState) => 1)
            case SWAP2 => Some((s:OKState) => 1)
            case SWAP3 => Some((s:OKState) => 1)
            case SWAP4 => Some((s:OKState) => 1)
            case SWAP5 => Some((s:OKState) => 1)
            case SWAP6 => Some((s:OKState) => 1)
            case SWAP7 => Some((s:OKState) => 1)
            case SWAP8 => Some((s:OKState) => 1)
            case SWAP9 => Some((s:OKState) => 1)
            case SWAP10 => Some((s:OKState) => 1)
            case SWAP11 => Some((s:OKState) => 1)
            case SWAP12 => Some((s:OKState) => 1)
            case SWAP13 => Some((s:OKState) => 1)
            case SWAP14 => Some((s:OKState) => 1)
            case SWAP15 => Some((s:OKState) => 1)
            case SWAP16 => Some((s:OKState) => 1)
            // 0xA0s: Log operations
            // else if LOG0 <=opcode <= LOG4 => (s:OKState
            //   var k => opcode - LOG0) as int; evalLOG(st,k)
            // 0xf0
            case CREATE => Some((s:OKState) => 1)
            case CALL => Some((s:OKState) => 1)
            case CALLCODE => Some((s:OKState) => 1)
            case RETURN => Some((s:OKState) => 1)
            case DELEGATECALL => Some((s:OKState) => 1)
            // case CREATE2 => Some((s:OKState) => 1)
            case STATICCALL => Some((s:OKState) => 1)
            case REVERT => Some((s:OKState) => 1)
            case SELFDESTRUCT => Some((s:OKState) => 1)
            case _ =>  None
    } 

    /** The Berlin gas cost function.
     *
     *  see H.1 page 29, BERLIN VERSION 3078285 – 2022-07-13.
     */
    function method GasBerlin(op: u8): Option<OKState -> nat> {
        match op 
        case STOP => Some((s:OKState) => G_ZERO as nat)
        case ADD => Some((s:OKState) => G_VERYLOW)
        case MUL => Some((s:OKState) => G_LOW)
        case SUB => Some((s:OKState) => G_VERYLOW)
        case DIV => Some((s:OKState) => G_LOW)
        case SDIV => Some((s:OKState) => G_LOW)
        case MOD => Some((s:OKState) => G_LOW)
        case SMOD => Some((s:OKState) => G_LOW)
        case ADDMOD => Some((s:OKState) => G_MID)
        case MULMOD => Some((s:OKState) => G_MID)
        // EXP => Some((s:OKState) => 1)
        case SIGNEXTEND => Some((s:OKState) => G_LOW)
        // 0x10s: Comparison & Bitwise Logic
        case LT => Some((s:OKState) => G_VERYLOW)
        case GT => Some((s:OKState) => G_VERYLOW)
        case SLT => Some((s:OKState) => G_VERYLOW)
        case SGT => Some((s:OKState) => G_VERYLOW)
        case EQ => Some((s:OKState) => G_VERYLOW)
        case ISZERO => Some((s:OKState) => G_VERYLOW)
        case AND => Some((s:OKState) => G_VERYLOW)
        case OR => Some((s:OKState) => G_VERYLOW)
        case XOR => Some((s:OKState) => G_VERYLOW)
        case NOT => Some((s:OKState) => G_VERYLOW)
        case BYTE => Some((s:OKState) => G_VERYLOW)
        case SHL => Some((s:OKState) => G_VERYLOW)
        case SHR => Some((s:OKState) => G_VERYLOW)
        // SAR => Some((s:OKState) => 1)
        // 0x20s
        //  KECCAK256 => Some((s:OKState) => 1)
        // 0x30s: Environment Information
        case ADDRESS => Some((s:OKState) => G_BASE)
        case BALANCE => Some((s:OKState) => G_BALANCE)
        case ORIGIN => Some((s:OKState) => G_BASE)
        case CALLER => Some((s:OKState) => G_BASE)
        case CALLVALUE => Some((s:OKState) => G_BASE)
        case CALLDATALOAD => Some((s:OKState) => G_VERYLOW)
        // CALLDATASIZE => Some((s:OKState) => 1)
        case CALLDATACOPY => Some((s:OKState) => G_COPY)
        // CODESIZE => Some((s:OKState) => 1)
        case CODECOPY => Some((s:OKState) => G_COPY)
        case GASPRICE => Some((s:OKState) => G_BASE)
        // EXTCODESIZE => Some((s:OKState) => 1)
        // EXTCODECOPY => Some((s:OKState) => 1)
        case RETURNDATASIZE => Some((s:OKState) => G_BASE)
        case RETURNDATACOPY => Some((s:OKState) => G_COPY)
        //  EXTCODEHASH => Some((s:OKState) => 1)
        // 0x40s: Block Information
        // BLOCKHASH => Some((s:OKState) => 1)
        case COINBASE => Some((s:OKState) => G_BASE)
        case TIMESTAMP => Some((s:OKState) => G_BASE)
        case NUMBER => Some((s:OKState) => G_BASE)
        case DIFFICULTY => Some((s:OKState) => G_BASE)
        case GASLIMIT => Some((s:OKState) => G_BASE)
        //  CHAINID => Some((s:OKState) => 1)
        //  SELFBALANCE => Some((s:OKState) => 1)
        // 0x50s: Stack, Memory, Storage and Flow
        case POP => Some((s:OKState) => G_BASE)
        case MLOAD => Some((s:OKState) => G_VERYLOW)
        case MSTORE => Some((s:OKState) => G_VERYLOW)
        case MSTORE8 => Some((s:OKState) => G_VERYLOW)
        // case SLOAD => Some((s:OKState) => G_HIGH)
        // case SSTORE => Some((s:OKState) => G_HIGH)
        case JUMP => Some((s:OKState) => G_MID)
        // JUMPI => Some((s:OKState) => 1)
        case PC => Some((s:OKState) => G_BASE)
        case MSIZE => Some((s:OKState) => G_BASE)
        case JUMPDEST => Some((s:OKState) => G_HIGH)
        // 0x60s & 0x70s: Push operations
        case PUSH1 => Some((s: OKState) => G_VERYLOW)
        case PUSH2 => Some((s:OKState) => G_VERYLOW)
        // PUSH3 => Some((s:OKState) => 1)
        // PUSH4 => Some((s:OKState) => 1)
        // PUSH5 => Some((s:OKState) => 1)
        // PUSH6 => Some((s:OKState) => 1)
        // PUSH7 => Some((s:OKState) => 1)
        // PUSH8 => Some((s:OKState) => 1)
        // PUSH9 => Some((s:OKState) => 1)
        // PUSH10 => Some((s:OKState) => 1)
        // PUSH11 => Some((s:OKState) => 1)
        // 0x80s: Duplicate operations
        case DUP1 => Some((s:OKState) => G_VERYLOW)
        case DUP2 => Some((s:OKState) => G_VERYLOW)
        case DUP3 => Some((s:OKState) => G_VERYLOW)
        case DUP4 => Some((s:OKState) => G_VERYLOW)
        case DUP5 => Some((s:OKState) => G_VERYLOW)
        case DUP6 => Some((s:OKState) => G_VERYLOW)
        case DUP7 => Some((s:OKState) => G_VERYLOW)
        case DUP8 => Some((s:OKState) => G_VERYLOW)
        case DUP9 => Some((s:OKState) => G_VERYLOW)
        case DUP10 => Some((s:OKState) => G_VERYLOW)
        case DUP11 => Some((s:OKState) => G_VERYLOW)
        case DUP12 => Some((s:OKState) => G_VERYLOW)
        case DUP13 => Some((s:OKState) => G_VERYLOW)
        case DUP14 => Some((s:OKState) => G_VERYLOW)
        case DUP15 => Some((s:OKState) => G_VERYLOW)
        case DUP16 => Some((s:OKState) => G_VERYLOW)
        // 0x90s: Exchange operations
        case SWAP1 => Some((s:OKState) => G_VERYLOW)
        case SWAP2 => Some((s:OKState) => G_VERYLOW)
        case SWAP3 => Some((s:OKState) => G_VERYLOW)
        case SWAP4 => Some((s:OKState) => G_VERYLOW)
        case SWAP5 => Some((s:OKState) => G_VERYLOW)
        case SWAP6 => Some((s:OKState) => G_VERYLOW)
        case SWAP7 => Some((s:OKState) => G_VERYLOW)
        case SWAP8 => Some((s:OKState) => G_VERYLOW)
        case SWAP9 => Some((s:OKState) => G_VERYLOW)
        case SWAP10 => Some((s:OKState) => G_VERYLOW)
        case SWAP11 => Some((s:OKState) => G_VERYLOW)
        case SWAP12 => Some((s:OKState) => G_VERYLOW)
        case SWAP13 => Some((s:OKState) => G_VERYLOW)
        case SWAP14 => Some((s:OKState) => G_VERYLOW)
        case SWAP15 => Some((s:OKState) => G_VERYLOW)
        case SWAP16 => Some((s:OKState) => G_VERYLOW)
        // 0xA0s: Log operations
        // else if LOG0 <=opcode <= LOG4 => Some((s:OKState))
        //   var k => Some(opcode - LOG0) as int; evalLOG(st,k))
        // 0xf0
        // CREATE => Some((s:OKState) => 1)
        // CALL => Some((s:OKState) => 1)
        // CALLCODE => Some((s:OKState) => 1)
        case RETURN => Some((s:OKState) => G_ZERO)
        // DELEGATECALL => Some((s:OKState) => 1)
        // CREATE2 => Some((s:OKState) => 1)
        // STATICCALL => Some((s:OKState) => 1)
        case REVERT => Some((s:OKState) => G_ZERO)
        case SELFDESTRUCT => Some((s:OKState) => 1)
        case _ => None 
    }

    /* this is the function C_mem (YP, page 28, BERLIN VERSION 3078285 – 2022-07-13) */
    function method
        memoryCost(mu_i: nat): nat
            {
                G_MEMORY * mu_i + ((mu_i * mu_i) / 512)
            }    
}

