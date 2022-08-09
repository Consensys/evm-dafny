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
include "util/EtraTypes.dfy"

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
    function method UseOneGas(op: u8, s: OKState): State
    {
        s.UseGas(1)
    }

    /** The Berlin gas cost function.
     *
     *  see H.1 page 29, BERLIN VERSION 3078285 – 2022-07-13.
     */
    function method GasBerlin(op: u8, s: OKState): State
    {
        match op
            case STOP => s.UseGas(G_ZERO)
            case ADD => s.UseGas(G_VERYLOW)
            case MUL => s.UseGas(G_LOW)
            case SUB => s.UseGas(G_VERYLOW)
            case DIV => s.UseGas(G_LOW)
            case SDIV => s.UseGas(G_LOW)
            case MOD => s.UseGas(G_LOW)
            case SMOD => s.UseGas(G_LOW)
            case ADDMOD => s.UseGas(G_MID)
            case MULMOD => s.UseGas(G_MID)
            case EXP => s.UseGas(G_EXP) // FIXME
            case SIGNEXTEND => s.UseGas(G_LOW)
            // 0x10s: Comparison & Bitwise Logic
            case LT => s.UseGas(G_VERYLOW)
            case GT => s.UseGas(G_VERYLOW)
            case SLT => s.UseGas(G_VERYLOW)
            case SGT => s.UseGas(G_VERYLOW)
            case EQ => s.UseGas(G_VERYLOW)
            case ISZERO => s.UseGas(G_VERYLOW)
            case AND => s.UseGas(G_VERYLOW)
            case OR => s.UseGas(G_VERYLOW)
            case XOR => s.UseGas(G_VERYLOW)
            case NOT => s.UseGas(G_VERYLOW)
            case BYTE => s.UseGas(G_VERYLOW)
            case SHL => s.UseGas(G_VERYLOW)
            case SHR => s.UseGas(G_VERYLOW)
            case SAR => s.UseGas(G_VERYLOW)
            // 0x20s
            //  KECCAK256 => s.UseGas(1)
            // 0x30s: Environment Information
            case ADDRESS => s.UseGas(G_BASE)
            case BALANCE => s.UseGas(G_BALANCE)
            case ORIGIN => s.UseGas(G_BASE)
            case CALLER => s.UseGas(G_BASE)
            case CALLVALUE => s.UseGas(G_BASE)
            case CALLDATALOAD => s.UseGas(G_VERYLOW)
            case CALLDATASIZE => s.UseGas(G_BASE)
            case CALLDATACOPY => s.UseGas(G_COPY)
            case CODESIZE => s.UseGas(G_BASE)
            case CODECOPY => s.UseGas(G_COPY)
            case GASPRICE => s.UseGas(G_BASE)
            // EXTCODESIZE => s.UseGas(1)
            // EXTCODECOPY => s.UseGas(1)
            case RETURNDATASIZE => s.UseGas(G_BASE)
            case RETURNDATACOPY => s.UseGas(G_COPY)
            //  EXTCODEHASH => s.UseGas(1)
            // 0x40s: Block Information
            // BLOCKHASH => s.UseGas(1)
            case COINBASE => s.UseGas(G_BASE)
            case TIMESTAMP => s.UseGas(G_BASE)
            case NUMBER => s.UseGas(G_BASE)
            case DIFFICULTY => s.UseGas(G_BASE)
            case GASLIMIT => s.UseGas(G_BASE)
            //  CHAINID => s.UseGas(1)
            //  SELFBALANCE => s.UseGas(1)
            // 0x50s: Stack, Memory, Storage and Flow
            case POP => s.UseGas(G_BASE)
            case MLOAD => s.UseGas(G_VERYLOW)
            case MSTORE => s.UseGas(G_VERYLOW)
            case MSTORE8 => s.UseGas(G_VERYLOW)
            case SLOAD => s.UseGas(G_HIGH) // for now
            case SSTORE => s.UseGas(G_HIGH) // for now
            case JUMP => s.UseGas(G_MID)
            case JUMPI => s.UseGas(1) // for now
            case PC => s.UseGas(G_BASE)
            case MSIZE => s.UseGas(G_BASE)
            case JUMPDEST => s.UseGas(G_HIGH)
            // 0x60s & 0x70s: Push operations
            case PUSH1 => s.UseGas(G_VERYLOW)
            case PUSH2 => s.UseGas(G_VERYLOW)
            case PUSH3 => s.UseGas(G_VERYLOW)
            case PUSH4 => s.UseGas(G_VERYLOW)
            case PUSH5 => s.UseGas(G_VERYLOW)
            case PUSH6 => s.UseGas(G_VERYLOW)
            case PUSH7 => s.UseGas(G_VERYLOW)
            case PUSH8 => s.UseGas(G_VERYLOW)
            case PUSH9 => s.UseGas(G_VERYLOW)
            case PUSH10 => s.UseGas(G_VERYLOW)
            case PUSH11 => s.UseGas(G_VERYLOW)
            case PUSH12 => s.UseGas(G_VERYLOW)
            case PUSH13 => s.UseGas(G_VERYLOW)
            case PUSH14 => s.UseGas(G_VERYLOW)
            case PUSH15 => s.UseGas(G_VERYLOW)
            case PUSH16 => s.UseGas(G_VERYLOW)
            case PUSH17 => s.UseGas(G_VERYLOW)
            case PUSH18 => s.UseGas(G_VERYLOW)
            case PUSH19 => s.UseGas(G_VERYLOW)
            case PUSH20 => s.UseGas(G_VERYLOW)
            case PUSH21 => s.UseGas(G_VERYLOW)
            case PUSH22 => s.UseGas(G_VERYLOW)
            case PUSH23 => s.UseGas(G_VERYLOW)
            case PUSH24 => s.UseGas(G_VERYLOW)
            case PUSH25 => s.UseGas(G_VERYLOW)
            case PUSH26 => s.UseGas(G_VERYLOW)
            case PUSH27 => s.UseGas(G_VERYLOW)
            case PUSH28 => s.UseGas(G_VERYLOW)
            case PUSH29 => s.UseGas(G_VERYLOW)
            case PUSH30 => s.UseGas(G_VERYLOW)
            case PUSH31 => s.UseGas(G_VERYLOW)
            case PUSH32 => s.UseGas(G_VERYLOW)
            // 0x80s: Duplicate operations
            case DUP1 => s.UseGas(G_VERYLOW)
            case DUP2 => s.UseGas(G_VERYLOW)
            case DUP3 => s.UseGas(G_VERYLOW)
            case DUP4 => s.UseGas(G_VERYLOW)
            case DUP5 => s.UseGas(G_VERYLOW)
            case DUP6 => s.UseGas(G_VERYLOW)
            case DUP7 => s.UseGas(G_VERYLOW)
            case DUP8 => s.UseGas(G_VERYLOW)
            case DUP9 => s.UseGas(G_VERYLOW)
            case DUP10 => s.UseGas(G_VERYLOW)
            case DUP11 => s.UseGas(G_VERYLOW)
            case DUP12 => s.UseGas(G_VERYLOW)
            case DUP13 => s.UseGas(G_VERYLOW)
            case DUP14 => s.UseGas(G_VERYLOW)
            case DUP15 => s.UseGas(G_VERYLOW)
            case DUP16 => s.UseGas(G_VERYLOW)
            // 0x90s: Exchange operations
            case SWAP1 => s.UseGas(G_VERYLOW)
            case SWAP2 => s.UseGas(G_VERYLOW)
            case SWAP3 => s.UseGas(G_VERYLOW)
            case SWAP4 => s.UseGas(G_VERYLOW)
            case SWAP5 => s.UseGas(G_VERYLOW)
            case SWAP6 => s.UseGas(G_VERYLOW)
            case SWAP7 => s.UseGas(G_VERYLOW)
            case SWAP8 => s.UseGas(G_VERYLOW)
            case SWAP9 => s.UseGas(G_VERYLOW)
            case SWAP10 => s.UseGas(G_VERYLOW)
            case SWAP11 => s.UseGas(G_VERYLOW)
            case SWAP12 => s.UseGas(G_VERYLOW)
            case SWAP13 => s.UseGas(G_VERYLOW)
            case SWAP14 => s.UseGas(G_VERYLOW)
            case SWAP15 => s.UseGas(G_VERYLOW)
            case SWAP16 => s.UseGas(G_VERYLOW)
            // 0xA0s: Log operations
            // else if LOG0 <=opcode <= LOG4 => Some((s:OKState))
            //   var k => Some(opcode - LOG0) as int; evalLOG(st,k))
            // 0xf0
            // CREATE => s.UseGas(1)
            // CALL => s.UseGas(1)
            // CALLCODE => s.UseGas(1)
            case RETURN => s.UseGas(G_ZERO)
            // DELEGATECALL => s.UseGas(1)
            // CREATE2 => s.UseGas(1)
            // STATICCALL => s.UseGas(1)
            case REVERT => s.UseGas(G_ZERO)
            case SELFDESTRUCT => s.UseGas(1)
            case _ => State.INVALID
    }
}
