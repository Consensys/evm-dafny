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
include "../evm.dfy"
include "../bytecode.dfy"
include "../gas.dfy"
include "../core/precompiled.dfy"

module EvmBerlin refines EVM {
    import opened Opcode
    import Bytecode
    import Gas
    import Precompiled

    /** An empty VM, with some gas.
     *
     *  @param  gas     The gas loaded in this EVM.
     *  @returns        An ready-to-use EVM.
     */
    function InitEmpty(gas: nat, code: seq<u8> := []) : (st:ExecutingState)
    requires |code| <= Code.MAX_CODE_SIZE
    {
        var tx := Context.DEFAULT;
        Create(tx, map[0:=WorldState.DefaultAccount()], gas, code)
    }

    /** An empty VM, with some initial gas and initial stack.
     *
     *  @param  gas     The gas loaded in this EVM.
     *  @returns        An ready-to-use EVM.
     */
    function Init(gas: nat, stk: seq<u256> := [], code: seq<u8> := []) : (st:ExecutingState)
    requires |code| <= Code.MAX_CODE_SIZE
    requires |stk| <= 1024
    {
        var tx := Context.Create(0,0,0,0,[],true,0,Context.Block.Info(0,0,0,0,0,0), Precompiled.DEFAULT);
        Create(tx, map[0:=WorldState.DefaultAccount()], gas, code, stk)
    }

    /** The gas cost semantics of an opcode.
     *
     *  @param op   The opcode to look up.
     *  @param st   An executing state.
     *  @returns    The new state obtained having consumed the gas that corresponds to
     *              the cost of `opcode` is `s`.
     */
    function OpGas(op: u8, st: ExecutingState): State {
        Gas.GasBerlin(op, st)
    }

    /** The semantics of opcodes.
     *
     *  @param op   The opcode to look up.
     *  @param st   Executing state to apply the opcode to.
     *  @returns    The new state obtained after applying the semantics
     *              of the opcode.
     *  @note       If an opcode is not supported, or there is not enough gas
     *              the returned state is INVALID.
     */
    function OpSem(op: u8, st: ExecutingState): State {
        match op
            case STOP => Bytecode.Stop(st)
            case ADD => Bytecode.Add(st)
            case MUL => Bytecode.Mul(st)
            case SUB => Bytecode.Sub(st)
            case DIV => Bytecode.Div(st)
            case SDIV => Bytecode.SDiv(st)
            case MOD => Bytecode.Mod(st)
            case SMOD => Bytecode.SMod(st)
            case ADDMOD => Bytecode.AddMod(st)
            case MULMOD => Bytecode.MulMod(st)
            case EXP => Bytecode.Exp(st)
            case SIGNEXTEND => Bytecode.SignExtend(st)
            // 0x10s: Comparison & Bitwise Logic
            case LT => Bytecode.Lt(st)
            case GT => Bytecode.Gt(st)
            case SLT => Bytecode.SLt(st)
            case SGT => Bytecode.SGt(st)
            case EQ => Bytecode.Eq(st)
            case ISZERO => Bytecode.IsZero(st)
            case AND => Bytecode.And(st)
            case OR => Bytecode.Or(st)
            case XOR => Bytecode.Xor(st)
            case NOT => Bytecode.Not(st)
            case BYTE => Bytecode.Byte(st)
            case SHL => Bytecode.Shl(st)
            case SHR => Bytecode.Shr(st)
            case SAR => Bytecode.Sar(st)
            // 0x20s
            case KECCAK256 => Bytecode.Keccak256(st)
            // 0x30s: Environment Information
            case ADDRESS => Bytecode.Address(st)
            case BALANCE => Bytecode.Balance(st)
            case ORIGIN => Bytecode.Origin(st)
            case CALLER => Bytecode.Caller(st)
            case CALLVALUE => Bytecode.CallValue(st)
            case CALLDATALOAD => Bytecode.CallDataLoad(st)
            case CALLDATASIZE => Bytecode.CallDataSize(st)
            case CALLDATACOPY => Bytecode.CallDataCopy(st)
            case CODESIZE => Bytecode.CodeSize(st)
            case CODECOPY => Bytecode.CodeCopy(st)
            case GASPRICE => Bytecode.GasPrice(st)
            case EXTCODESIZE => Bytecode.ExtCodeSize(st)
            case EXTCODECOPY => Bytecode.ExtCodeCopy(st)
            case RETURNDATASIZE => Bytecode.ReturnDataSize(st)
            case RETURNDATACOPY => Bytecode.ReturnDataCopy(st)
            case EXTCODEHASH => Bytecode.ExtCodeHash(st)
            // 0x40s: Block Information
            case BLOCKHASH => Bytecode.BlockHash(st)
            case COINBASE => Bytecode.CoinBase(st)
            case TIMESTAMP => Bytecode.TimeStamp(st)
            case NUMBER => Bytecode.Number(st)
            case DIFFICULTY => Bytecode.Difficulty(st)
            case GASLIMIT => Bytecode.GasLimit(st)
            case CHAINID => Bytecode.ChainID(st)
            case SELFBALANCE => Bytecode.SelfBalance(st)
            // 0x50s: Stack, Memory, Storage and Flow
            case POP => Bytecode.Pop(st)
            case MLOAD => Bytecode.MLoad(st)
            case MSTORE => Bytecode.MStore(st)
            case MSTORE8 => Bytecode.MStore8(st)
            case SLOAD => Bytecode.SLoad(st)
            case SSTORE => Bytecode.SStore(st)
            case JUMP => Bytecode.Jump(st)
            case JUMPI => Bytecode.JumpI(st)
            case PC => Bytecode.Pc(st)
            case MSIZE => Bytecode.MSize(st)
            case GAS => Bytecode.Gas(st)
            case JUMPDEST => Bytecode.JumpDest(st)
            // 0x60s & 0x70s: Push operations
            case PUSH1 => Bytecode.Push(st,1)
            case PUSH2 => Bytecode.Push(st,2)
            case PUSH3 => Bytecode.Push(st,3)
            case PUSH4 => Bytecode.Push(st,4)
            case PUSH5 => Bytecode.Push(st,5)
            case PUSH6 => Bytecode.Push(st,6)
            case PUSH7 => Bytecode.Push(st,7)
            case PUSH8 => Bytecode.Push(st,8)
            case PUSH9 => Bytecode.Push(st,9)
            case PUSH10 => Bytecode.Push(st,10)
            case PUSH11 => Bytecode.Push(st,11)
            case PUSH12 => Bytecode.Push(st,12)
            case PUSH13 => Bytecode.Push(st,13)
            case PUSH14 => Bytecode.Push(st,14)
            case PUSH15 => Bytecode.Push(st,15)
            case PUSH16 => Bytecode.Push(st,16)
            case PUSH17 => Bytecode.Push(st,17)
            case PUSH18 => Bytecode.Push(st,18)
            case PUSH19 => Bytecode.Push(st,19)
            case PUSH20 => Bytecode.Push(st,20)
            case PUSH21 => Bytecode.Push(st,21)
            case PUSH22 => Bytecode.Push(st,22)
            case PUSH23 => Bytecode.Push(st,23)
            case PUSH24 => Bytecode.Push(st,24)
            case PUSH25 => Bytecode.Push(st,25)
            case PUSH26 => Bytecode.Push(st,26)
            case PUSH27 => Bytecode.Push(st,27)
            case PUSH28 => Bytecode.Push(st,28)
            case PUSH29 => Bytecode.Push(st,29)
            case PUSH30 => Bytecode.Push(st,30)
            case PUSH31 => Bytecode.Push(st,31)
            case PUSH32 => Bytecode.Push(st,32)
            // 0x80s: Duplicate operations
            case DUP1 => Bytecode.Dup(st, 1)
            case DUP2 => Bytecode.Dup(st, 2)
            case DUP3 => Bytecode.Dup(st, 3)
            case DUP4 => Bytecode.Dup(st, 4)
            case DUP5 => Bytecode.Dup(st, 5)
            case DUP6 => Bytecode.Dup(st, 6)
            case DUP7 => Bytecode.Dup(st, 7)
            case DUP8 => Bytecode.Dup(st, 8)
            case DUP9 => Bytecode.Dup(st, 9)
            case DUP10 => Bytecode.Dup(st, 10)
            case DUP11 => Bytecode.Dup(st, 11)
            case DUP12 => Bytecode.Dup(st, 12)
            case DUP13 => Bytecode.Dup(st, 13)
            case DUP14 => Bytecode.Dup(st, 14)
            case DUP15 => Bytecode.Dup(st, 15)
            case DUP16 => Bytecode.Dup(st, 16)
            // 0x90s: Exchange operations
            case SWAP1 => Bytecode.Swap(st, 1)
            case SWAP2 => Bytecode.Swap(st, 2)
            case SWAP3 => Bytecode.Swap(st, 3)
            case SWAP4 => Bytecode.Swap(st, 4)
            case SWAP5 => Bytecode.Swap(st, 5)
            case SWAP6 => Bytecode.Swap(st, 6)
            case SWAP7 => Bytecode.Swap(st, 7)
            case SWAP8 => Bytecode.Swap(st, 8)
            case SWAP9 => Bytecode.Swap(st, 9)
            case SWAP10 => Bytecode.Swap(st, 10)
            case SWAP11 => Bytecode.Swap(st, 11)
            case SWAP12 => Bytecode.Swap(st, 12)
            case SWAP13 => Bytecode.Swap(st, 13)
            case SWAP14 => Bytecode.Swap(st, 14)
            case SWAP15 => Bytecode.Swap(st, 15)
            case SWAP16 => Bytecode.Swap(st, 16)
            // 0xA0s: Log operations
            case LOG0 => Bytecode.LogN(st,0)
            case LOG1 => Bytecode.LogN(st,1)
            case LOG2 => Bytecode.LogN(st,2)
            case LOG3 => Bytecode.LogN(st,3)
            case LOG4 => Bytecode.LogN(st,4)
            // 0xf0
            case CREATE => Bytecode.Create(st)
            case CALL => Bytecode.Call(st)
            case CALLCODE => Bytecode.CallCode(st)
            case RETURN => Bytecode.Return(st)
            case DELEGATECALL => Bytecode.DelegateCall(st)
            case CREATE2 => Bytecode.Create2(st)
            case STATICCALL => Bytecode.StaticCall(st)
            case REVERT => Bytecode.Revert(st)
            case SELFDESTRUCT => Bytecode.SelfDestruct(st)
            case _ => ERROR(INVALID_OPCODE)
    }
}
