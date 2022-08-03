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

module EvmBerlin refines EVM {
    import opened Opcode
    import Bytecode
    import Gas

    /** An empty VM, with some gas.
     *
     *  @param  g   The gas loaded in this EVM.
     *  @returns    An ready-to-use EVM.
     */
    function method InitEmpty(g: nat): State
        ensures !InitEmpty(g).IsFailure()
    {
        var tx := Context.Create(0x0,0,0,[],0); 
        Create(tx, map[], g, [])
    }

    /** The gas cost of each opcode. */
    const GAS := Gas.GAS_ONE

    function method GAS2(op: u8): Option<OKState -> nat> {
        Gas.GasOne(op)
    }

    // function method SupportedOpcode(op: u8): bool {
    //     match op 
    //         case STOP =>  true 
    //         case ADD =>  true 
    //         case MUL =>  true 
    //         case SUB =>  true 
    //         case DIV =>  true 
    //         case SDIV =>  true 
    //         case MOD =>  true 
    //         case SMOD =>  true 
    //         case ADDMOD =>  true 
    //         case MULMOD =>  true 
    //         //  EXP =>  true 
    //         //  SIGNEXTEND =>  true 
    //         // 0x10s: Comparison & Bitwise Logic
    //         case LT =>  true 
    //         case GT =>  true 
    //         case SLT =>  true 
    //         case SGT =>  true 
    //         case EQ =>  true 
    //         case ISZERO =>  true 
    //         case AND =>  true 
    //         case OR =>  true 
    //         case XOR =>  true 
    //         case NOT =>  true 
    //         case BYTE =>  true 
    //         case SHL =>  true 
    //         case SHR =>  true 
    //         //  SAR =>  true 
    //         // 0x20s
    //         //  KECCAK256 =>  true 
    //         // 0x30s: Environment Information
    //         case ADDRESS =>  true 
    //         //  BALANCE =>  true 
    //         case ORIGIN =>  true 
    //         case CALLER =>  true 
    //         case CALLVALUE =>  true 
    //         case CALLDATALOAD =>  true 
    //         case CALLDATASIZE =>  true 
    //         case CALLDATACOPY =>  true 
    //         case CODESIZE =>  true 
    //         case CODECOPY =>  true 
    //         case GASPRICE =>  true 
    //         //  EXTCODESIZE =>  true 
    //         //  EXTCODECOPY =>  true 
    //         //  RETURNDATASIZE =>  true 
    //         //  RETURNDATACOPY =>  true 
    //         //  EXTCODEHASH =>  true 
    //         // 0x40s: Block Information
    //         //  BLOCKHASH =>  true 
    //         //  COINBASE =>  true 
    //         //  TIMESTAMP =>  true 
    //         //  NUMBER =>  true 
    //         //  DIFFICULTY =>  true 
    //         //  GASLIMIT =>  true 
    //         //  CHAINID =>  true 
    //         //  SELFBALANCE =>  true 
    //         // 0x50s: Stack, Memory, Storage and Flow
    //         case POP =>  true 
    //         case MLOAD =>  true 
    //         case MSTORE =>  true 
    //         case MSTORE8 =>  true 
    //         case SLOAD =>  true 
    //         case SSTORE =>  true 
    //         case JUMP =>  true 
    //         case JUMPI =>  true 
    //         case PC =>  true 
    //         case JUMPDEST =>  true 
    //         // 0x60s & 0x70s: Push operations
    //         case PUSH1 =>  true
    //         case PUSH2 =>  true
    //         case PUSH3 =>  true
    //         case PUSH4 =>  true
    //         // case PUSH5 =>  (s: OKState) => Push(s,5)
    //         // case PUSH6 =>  (s: OKState) => Push(s,6)
    //         // case PUSH7 =>  (s: OKState) => Push(s,7)
    //         // case PUSH8 =>  (s: OKState) => Push(s,8)
    //         // case PUSH9 =>  (s: OKState) => Push(s,9)
    //         // case PUSH10 =>  (s: OKState) => Push(s,10)
    //         // case PUSH11 =>  (s: OKState) => Push(s,11)
    //         // case PUSH12 =>  (s: OKState) => Push(s,12)
    //         // case PUSH13 =>  (s: OKState) => Push(s,13)
    //         // case PUSH14 =>  (s: OKState) => Push(s,14)
    //         // case PUSH15 =>  (s: OKState) => Push(s,15)
    //         // case PUSH16 =>  (s: OKState) => Push(s,16)
    //         // case PUSH17 =>  (s: OKState) => Push(s,17)
    //         // case PUSH18 =>  (s: OKState) => Push(s,18)
    //         // case PUSH19 =>  (s: OKState) => Push(s,19)
    //         // case PUSH20 =>  (s: OKState) => Push(s,20)
    //         // case PUSH21 =>  (s: OKState) => Push(s,21)
    //         // case PUSH22 =>  (s: OKState) => Push(s,22)
    //         // case PUSH23 =>  (s: OKState) => Push(s,23)
    //         // case PUSH24 =>  (s: OKState) => Push(s,24)
    //         // case PUSH25 =>  (s: OKState) => Push(s,25)
    //         // case PUSH26 =>  (s: OKState) => Push(s,26)
    //         // case PUSH27 =>  (s: OKState) => Push(s,27)
    //         // case PUSH28 =>  (s: OKState) => Push(s,28)
    //         // case PUSH29 =>  (s: OKState) => Push(s,29)
    //         // case PUSH30 =>  (s: OKState) => Push(s,30)
    //         // case PUSH31 =>  (s: OKState) => Push(s,31)
    //         // case PUSH32 =>  (s: OKState) => Push(s,32)
    //         // 0x80s: Duplicate operations
    //         case DUP1 =>  true 
    //         case DUP2 =>  true 
    //         case DUP3 =>  true 
    //         case DUP4 =>  true 
    //         case DUP5 =>  true 
    //         case DUP6 =>  true 
    //         case DUP7 =>  true 
    //         case DUP8 =>  true 
    //         case DUP9 =>  true 
    //         case DUP10 =>  true 
    //         case DUP11 =>  true 
    //         case DUP12 =>  true 
    //         case DUP13 =>  true 
    //         case DUP14 =>  true 
    //         case DUP15 =>  true 
    //         case DUP16 =>  true 
    //         // 0x90s: Exchange operations
    //         case SWAP1 =>  true 
    //         case SWAP2 =>  true 
    //         case SWAP3 =>  true 
    //         case SWAP4 =>  true 
    //         case SWAP5 =>  true 
    //         case SWAP6 =>  true  
    //         case SWAP7 =>  true 
    //         case SWAP8 =>  true 
    //         case SWAP9 =>  true 
    //         case SWAP10 =>  true 
    //         case SWAP11 =>  true 
    //         case SWAP12 =>  true 
    //         case SWAP13 =>  true 
    //         case SWAP14 =>  true 
    //         case SWAP15 =>  true 
    //         case SWAP16 =>  true 
    //         // 0xA0s: Log operations
    //         // else if LOG0 <=case opcode <= LOG4 =>  (s:OKState
    //         //   var k =>  case opcode - LOG0) as int; evalLOG(st,k)
    //         // 0xf0
    //         //  CREATE =>  true 
    //         //  CALL =>  true 
    //         //  CALLCODE =>  true 
    //         case RETURN =>  true 
    //         // DELEGATECALL =>  true 
    //         // CREATE2 =>  true 
    //         // STATICCALL =>  true 
    //         // case REVERT =>  true 
    //         // SELFDESTRUCT := true 
    //         case _ => false
    // }

    function method SEMANTICS2(op: u8): Option<OKState -> State> 
    {
        match op
            case STOP =>  Some((s:OKState) => Bytecode.Stop(s))
            case ADD =>  Some((s:OKState) => Bytecode.Add(s))
            case MUL =>  Some((s:OKState) => Bytecode.Mul(s))
            case SUB =>  Some((s:OKState) => Bytecode.Sub(s))
            case DIV =>  Some((s:OKState) => Bytecode.Div(s))
            case SDIV =>  Some((s:OKState) => Bytecode.SDiv(s))
            case MOD =>  Some((s:OKState) => Bytecode.Mod(s))
            case SMOD =>  Some((s:OKState) => Bytecode.SMod(s))
            case ADDMOD =>  Some((s:OKState) => Bytecode.AddMod(s))
            case MULMOD =>  Some((s:OKState) => Bytecode.MulMod(s))
            //  EXP =>  Some((s:OKState) => Bytecode.evalEXP(s),)
            //  SIGNEXTEND =>  Some((s:OKState) => Bytecode.evalSIGNEXTEND(s),)
            // 0x10s: Comparison & Bitwise Logic
            case LT =>  Some((s:OKState) => Bytecode.Lt(s))
            case GT =>  Some((s:OKState) => Bytecode.Gt(s))
            case SLT =>  Some((s:OKState) => Bytecode.SLt(s))
            case SGT =>  Some((s:OKState) => Bytecode.SGt(s))
            case EQ =>  Some((s:OKState) => Bytecode.Eq(s))
            case ISZERO =>  Some((s:OKState) => Bytecode.IsZero(s))
            case AND =>  Some((s:OKState) => Bytecode.And(s))
            case OR =>  Some((s:OKState) => Bytecode.Or(s))
            case XOR =>  Some((s:OKState) => Bytecode.Xor(s))
            case NOT =>  Some((s:OKState) => Bytecode.Not(s))
            case BYTE =>  Some((s:OKState) => Bytecode.Byte(s))
            case SHL =>  Some((s:OKState) => Bytecode.Shl(s))
            case SHR =>  Some((s:OKState) => Bytecode.Shr(s))
            //  SAR =>  Some((s:OKState) => Bytecode.evalSAR(s),)
            // 0x20s
            //  KECCAK256 =>  Some((s:OKState) => Bytecode.evalKECCAK256(s),)
            // 0x30s: Environment Information
            case ADDRESS =>  Some((s:OKState) => Bytecode.Address(s))
            //  BALANCE =>  Some((s:OKState) => Bytecode.evalBALANCE(s),)
            case ORIGIN =>  Some((s:OKState) => Bytecode.Origin(s))
            case CALLER =>  Some((s:OKState) => Bytecode.Caller(s))
            case CALLVALUE =>  Some((s:OKState) => Bytecode.CallValue(s))
            case CALLDATALOAD =>  Some((s:OKState) => Bytecode.CallDataLoad(s))
            case CALLDATASIZE =>  Some((s:OKState) => Bytecode.CallDataSize(s))
            case CALLDATACOPY =>  Some((s:OKState) => Bytecode.CallDataCopy(s))
            case CODESIZE =>  Some((s:OKState) => Bytecode.CodeSize(s))
            case CODECOPY =>  Some((s:OKState) => Bytecode.CodeCopy(s))
            case GASPRICE =>  Some((s:OKState) => Bytecode.GasPrice(s))
            //  EXTCODESIZE =>  Some((s:OKState) => Bytecode.evalEXTCODESIZE(s),)
            //  EXTCODECOPY =>  Some((s:OKState) => Bytecode.evalEXTCODECOPY(s),)
            //  RETURNDATASIZE =>  Some((s:OKState) => Bytecode.evalRETURNDATASIZE(s),)
            //  RETURNDATACOPY =>  Some((s:OKState) => Bytecode.evalRETURNDATACOPY(s),)
            //  EXTCODEHASH =>  Some((s:OKState) => Bytecode.evalEXTCODEHASH(s),)
            // 0x40s: Block Information
            //  BLOCKHASH =>  Some((s:OKState) => Bytecode.evalBLOCKHASH(s),)
            //  COINBASE =>  Some((s:OKState) => Bytecode.evalCOINBASE(s),)
            //  TIMESTAMP =>  Some((s:OKState) => Bytecode.evalTIMESTAMP(s),)
            //  NUMBER =>  Some((s:OKState) => Bytecode.evalNUMBER(s),)
            //  DIFFICULTY =>  Some((s:OKState) => Bytecode.evalDIFFICULTY(s),)
            //  GASLIMIT =>  Some((s:OKState) => Bytecode.evalGASLIMIT(s),)
            //  CHAINID =>  Some((s:OKState) => Bytecode.evalCHAINID(s),)
            //  SELFBALANCE =>  Some((s:OKState) => Bytecode.evalSELFBALANCE(s),)
            // 0x50s: Stack, Memory, Storage and Flow
            case POP =>  Some((s:OKState) => Bytecode.Pop(s))
            case MLOAD =>  Some((s:OKState) => Bytecode.MLoad(s))
            case MSTORE =>  Some((s:OKState) => Bytecode.MStore(s))
            case MSTORE8 =>  Some((s:OKState) => Bytecode.MStore8(s))
            case SLOAD =>  Some((s:OKState) => Bytecode.SLoad(s))
            case SSTORE =>  Some((s:OKState) => Bytecode.SStore(s))
            case JUMP =>  Some((s:OKState) => Bytecode.Jump(s))
            case JUMPI =>  Some((s:OKState) => Bytecode.JumpI(s))
            case PC =>  Some((s:OKState) => if s.PC() <= MAX_U256 then Bytecode.Pc(s) else State.INVALID)
            case JUMPDEST =>  Some((s:OKState) => Bytecode.JumpDest(s))
            // 0x60s & 0x70s: Push operations
            case PUSH1 =>  Some((s: OKState) => Push(s,1))
            case PUSH2 =>  Some((s: OKState) => Push(s,2))
            case PUSH3 =>  Some((s: OKState) => Push(s,3))
            case PUSH4 =>  Some((s: OKState) => Push(s,4))
            // case PUSH5 =>  (s: OKState) => Push(s,5)
            // case PUSH6 =>  (s: OKState) => Push(s,6)
            // case PUSH7 =>  (s: OKState) => Push(s,7)
            // case PUSH8 =>  (s: OKState) => Push(s,8)
            // case PUSH9 =>  (s: OKState) => Push(s,9)
            // case PUSH10 =>  (s: OKState) => Push(s,10)
            // case PUSH11 =>  (s: OKState) => Push(s,11)
            // case PUSH12 =>  (s: OKState) => Push(s,12)
            // case PUSH13 =>  (s: OKState) => Push(s,13)
            // case PUSH14 =>  (s: OKState) => Push(s,14)
            // case PUSH15 =>  (s: OKState) => Push(s,15)
            // case PUSH16 =>  (s: OKState) => Push(s,16)
            // case PUSH17 =>  (s: OKState) => Push(s,17)
            // case PUSH18 =>  (s: OKState) => Push(s,18)
            // case PUSH19 =>  (s: OKState) => Push(s,19)
            // case PUSH20 =>  (s: OKState) => Push(s,20)
            // case PUSH21 =>  (s: OKState) => Push(s,21)
            // case PUSH22 =>  (s: OKState) => Push(s,22)
            // case PUSH23 =>  (s: OKState) => Push(s,23)
            // case PUSH24 =>  (s: OKState) => Push(s,24)
            // case PUSH25 =>  (s: OKState) => Push(s,25)
            // case PUSH26 =>  (s: OKState) => Push(s,26)
            // case PUSH27 =>  (s: OKState) => Push(s,27)
            // case PUSH28 =>  (s: OKState) => Push(s,28)
            // case PUSH29 =>  (s: OKState) => Push(s,29)
            // case PUSH30 =>  (s: OKState) => Push(s,30)
            // case PUSH31 =>  (s: OKState) => Push(s,31)
            // case PUSH32 =>  (s: OKState) => Push(s,32)
            // 0x80s: Duplicate operations
            case DUP1 =>  Some((s:OKState) => Bytecode.Dup(s, 1))
            case DUP2 =>  Some((s:OKState) => Bytecode.Dup(s, 2))
            case DUP3 =>  Some((s:OKState) => Bytecode.Dup(s, 3))
            case DUP4 =>  Some((s:OKState) => Bytecode.Dup(s, 4))
            case DUP5 =>  Some((s:OKState) => Bytecode.Dup(s, 5))
            case DUP6 =>  Some((s:OKState) => Bytecode.Dup(s, 6))
            case DUP7 =>  Some((s:OKState) => Bytecode.Dup(s, 7))
            case DUP8 =>  Some((s:OKState) => Bytecode.Dup(s, 8))
            case DUP9 =>  Some((s:OKState) => Bytecode.Dup(s, 9))
            case DUP10 =>  Some((s:OKState) => Bytecode.Dup(s, 10))
            case DUP11 =>  Some((s:OKState) => Bytecode.Dup(s, 11))
            case DUP12 =>  Some((s:OKState) => Bytecode.Dup(s, 12))
            case DUP13 =>  Some((s:OKState) => Bytecode.Dup(s, 13))
            case DUP14 =>  Some((s:OKState) => Bytecode.Dup(s, 14))
            case DUP15 =>  Some((s:OKState) => Bytecode.Dup(s, 15))
            case DUP16 =>  Some((s:OKState) => Bytecode.Dup(s, 16))
            // 0x90s: Exchange operations
            case SWAP1 =>  Some((s:OKState) => Bytecode.Swap(s, 1))
            case SWAP2 =>  Some((s:OKState) => Bytecode.Swap(s, 2))
            case SWAP3 =>  Some((s:OKState) => Bytecode.Swap(s, 3))
            case SWAP4 =>  Some((s:OKState) => Bytecode.Swap(s, 4))
            case SWAP5 =>  Some((s:OKState) => Bytecode.Swap(s, 5))
            case SWAP6 =>  Some((s:OKState) => Bytecode.Swap(s, 6))
            case SWAP7 =>  Some((s:OKState) => Bytecode.Swap(s, 7))
            case SWAP8 =>  Some((s:OKState) => Bytecode.Swap(s, 8))
            case SWAP9 =>  Some((s:OKState) => Bytecode.Swap(s, 9))
            case SWAP10 =>  Some((s:OKState) => Bytecode.Swap(s, 10))
            case SWAP11 =>  Some((s:OKState) => Bytecode.Swap(s, 11))
            case SWAP12 =>  Some((s:OKState) => Bytecode.Swap(s, 12))
            case SWAP13 =>  Some((s:OKState) => Bytecode.Swap(s, 13))
            case SWAP14 =>  Some((s:OKState) => Bytecode.Swap(s, 14))
            case SWAP15 =>  Some((s:OKState) => Bytecode.Swap(s, 15))
            case SWAP16 =>  Some((s:OKState) => Bytecode.Swap(s, 16))
            // 0xA0s: Log operations
            // else if LOG0 <=case opcode <= LOG4 =>  (s:OKState
            //   var k =>  case opcode - LOG0) as int; evalLOG(st,k)
            // 0xf0
            //  CREATE =>  Some((s:OKState) => Bytecode.evalCREATE(s),)
            //  CALL =>  Some((s:OKState) => Bytecode.evalCALL(s),)
            //  CALLCODE =>  Some((s:OKState) => Bytecode.evalCALLCODE(s),)
            case RETURN =>  Some((s:OKState) => Bytecode.Return(s))
            // DELEGATECALL =>  Some((s:OKState) => Bytecode.evalDELEGATECALL(s),)
            // CREATE2 =>  Some((s:OKState) => Bytecode.evalCREATE2(s),)
            // STATICCALL =>  Some((s:OKState) => Bytecode.evalSTATICCALL(s),)
            // case REVERT =>  Some((s:OKState) => Bytecode.Revert(s))
            // SELFDESTRUCT := Some((s:OKState) => Bytecode.evalSELFDESTRUCT(s),)
            case _ => None
    }

    /** The semantics of each opcode. */
    const SEMANTICS := map[
        Opcode.STOP := (s:OKState) => Bytecode.Stop(s),
        Opcode.ADD := (s:OKState) => Bytecode.Add(s),
        Opcode.MUL := (s:OKState) => Bytecode.Mul(s),
        Opcode.SUB := (s:OKState) => Bytecode.Sub(s),
        Opcode.DIV := (s:OKState) => Bytecode.Div(s),
        Opcode.SDIV := (s:OKState) => Bytecode.SDiv(s),
        Opcode.MOD := (s:OKState) => Bytecode.Mod(s),
        Opcode.SMOD := (s:OKState) => Bytecode.SMod(s),
        Opcode.ADDMOD := (s:OKState) => Bytecode.AddMod(s),
        Opcode.MULMOD := (s:OKState) => Bytecode.MulMod(s),
        //  EXP := (s:OKState) => Bytecode.evalEXP(s),
        //  SIGNEXTEND := (s:OKState) => Bytecode.evalSIGNEXTEND(s),
        // 0x10s: Comparison & Bitwise Logic
        Opcode.LT := (s:OKState) => Bytecode.Lt(s),
        Opcode.GT := (s:OKState) => Bytecode.Gt(s),
        Opcode.SLT := (s:OKState) => Bytecode.SLt(s),
        Opcode.SGT := (s:OKState) => Bytecode.SGt(s),
        Opcode.EQ := (s:OKState) => Bytecode.Eq(s),
        Opcode.ISZERO := (s:OKState) => Bytecode.IsZero(s),
        Opcode.AND := (s:OKState) => Bytecode.And(s),
        Opcode.OR := (s:OKState) => Bytecode.Or(s),
        Opcode.XOR := (s:OKState) => Bytecode.Xor(s),
        Opcode.NOT := (s:OKState) => Bytecode.Not(s),
        Opcode.BYTE := (s:OKState) => Bytecode.Byte(s),
        Opcode.SHL := (s:OKState) => Bytecode.Shl(s),
        Opcode.SHR := (s:OKState) => Bytecode.Shr(s),
        //  SAR := (s:OKState) => Bytecode.evalSAR(s),
        // 0x20s
        //  KECCAK256 := (s:OKState) => Bytecode.evalKECCAK256(s),
        // 0x30s: Environment Information
        Opcode.ADDRESS := (s:OKState) => Bytecode.Address(s),
        //  BALANCE := (s:OKState) => Bytecode.evalBALANCE(s),
        Opcode.ORIGIN := (s:OKState) => Bytecode.Origin(s),
        Opcode.CALLER := (s:OKState) => Bytecode.Caller(s),
        Opcode.CALLVALUE := (s:OKState) => Bytecode.CallValue(s),
        Opcode.CALLDATALOAD := (s:OKState) => Bytecode.CallDataLoad(s),
        Opcode.CALLDATASIZE := (s:OKState) => Bytecode.CallDataSize(s),
        Opcode.CALLDATACOPY := (s:OKState) => Bytecode.CallDataCopy(s),
        Opcode.CODESIZE := (s:OKState) => Bytecode.CodeSize(s),
        Opcode.CODECOPY := (s:OKState) => Bytecode.CodeCopy(s),
        Opcode.GASPRICE := (s:OKState) => Bytecode.GasPrice(s),
        //  EXTCODESIZE := (s:OKState) => Bytecode.evalEXTCODESIZE(s),
        //  EXTCODECOPY := (s:OKState) => Bytecode.evalEXTCODECOPY(s),
        //  RETURNDATASIZE := (s:OKState) => Bytecode.evalRETURNDATASIZE(s),
        //  RETURNDATACOPY := (s:OKState) => Bytecode.evalRETURNDATACOPY(s),
        //  EXTCODEHASH := (s:OKState) => Bytecode.evalEXTCODEHASH(s),
        // 0x40s: Block Information
        //  BLOCKHASH := (s:OKState) => Bytecode.evalBLOCKHASH(s),
        //  COINBASE := (s:OKState) => Bytecode.evalCOINBASE(s),
        //  TIMESTAMP := (s:OKState) => Bytecode.evalTIMESTAMP(s),
        //  NUMBER := (s:OKState) => Bytecode.evalNUMBER(s),
        //  DIFFICULTY := (s:OKState) => Bytecode.evalDIFFICULTY(s),
        //  GASLIMIT := (s:OKState) => Bytecode.evalGASLIMIT(s),
        //  CHAINID := (s:OKState) => Bytecode.evalCHAINID(s),
        //  SELFBALANCE := (s:OKState) => Bytecode.evalSELFBALANCE(s),
        // 0x50s: Stack, Memory, Storage and Flow
        Opcode.POP := (s:OKState) => Bytecode.Pop(s),
        Opcode.MLOAD := (s:OKState) => Bytecode.MLoad(s),
        Opcode.MSTORE := (s:OKState) => Bytecode.MStore(s),
        Opcode.MSTORE8 := (s:OKState) => Bytecode.MStore8(s),
        Opcode.SLOAD := (s:OKState) => Bytecode.SLoad(s),
        Opcode.SSTORE := (s:OKState) => Bytecode.SStore(s),
        Opcode.JUMP := (s:OKState) => Bytecode.Jump(s),
        Opcode.JUMPI := (s:OKState) => Bytecode.JumpI(s),
        Opcode.PC := (s:OKState) => if s.PC() <= MAX_U256 then Bytecode.Pc(s) else State.INVALID,
        Opcode.JUMPDEST := (s:OKState) => Bytecode.JumpDest(s),
        // 0x60s & 0x70s: Push operations
        Opcode.PUSH1 := (s: OKState) => Push(s,1),
        Opcode.PUSH2 := (s: OKState) => Push(s,2),
        Opcode.PUSH3 := (s: OKState) => Push(s,3),
        Opcode.PUSH4 := (s: OKState) => Push(s,4),
        // Opcode.PUSH5 := (s: OKState) => Push(s,5),
        // Opcode.PUSH6 := (s: OKState) => Push(s,6),
        // Opcode.PUSH7 := (s: OKState) => Push(s,7),
        // Opcode.PUSH8 := (s: OKState) => Push(s,8),
        // Opcode.PUSH9 := (s: OKState) => Push(s,9),
        // Opcode.PUSH10 := (s: OKState) => Push(s,10),
        // Opcode.PUSH11 := (s: OKState) => Push(s,11),
        // Opcode.PUSH12 := (s: OKState) => Push(s,12),
        // Opcode.PUSH13 := (s: OKState) => Push(s,13),
        // Opcode.PUSH14 := (s: OKState) => Push(s,14),
        // Opcode.PUSH15 := (s: OKState) => Push(s,15),
        // Opcode.PUSH16 := (s: OKState) => Push(s,16),
        // Opcode.PUSH17 := (s: OKState) => Push(s,17),
        // Opcode.PUSH18 := (s: OKState) => Push(s,18),
        // Opcode.PUSH19 := (s: OKState) => Push(s,19),
        // Opcode.PUSH20 := (s: OKState) => Push(s,20),
        // Opcode.PUSH21 := (s: OKState) => Push(s,21),
        // Opcode.PUSH22 := (s: OKState) => Push(s,22),
        // Opcode.PUSH23 := (s: OKState) => Push(s,23),
        // Opcode.PUSH24 := (s: OKState) => Push(s,24),
        // Opcode.PUSH25 := (s: OKState) => Push(s,25),
        // Opcode.PUSH26 := (s: OKState) => Push(s,26),
        // Opcode.PUSH27 := (s: OKState) => Push(s,27),
        // Opcode.PUSH28 := (s: OKState) => Push(s,28),
        // Opcode.PUSH29 := (s: OKState) => Push(s,29),
        // Opcode.PUSH30 := (s: OKState) => Push(s,30),
        // Opcode.PUSH31 := (s: OKState) => Push(s,31),
        // Opcode.PUSH32 := (s: OKState) => Push(s,32),
        // 0x80s: Duplicate operations
        Opcode.DUP1 := (s:OKState) => Bytecode.Dup(s, 1),
        Opcode.DUP2 := (s:OKState) => Bytecode.Dup(s, 2),
        Opcode.DUP3 := (s:OKState) => Bytecode.Dup(s, 3),
        Opcode.DUP4 := (s:OKState) => Bytecode.Dup(s, 4),
        Opcode.DUP5 := (s:OKState) => Bytecode.Dup(s, 5),
        Opcode.DUP6 := (s:OKState) => Bytecode.Dup(s, 6),
        Opcode.DUP7 := (s:OKState) => Bytecode.Dup(s, 7),
        Opcode.DUP8 := (s:OKState) => Bytecode.Dup(s, 8),
        Opcode.DUP9 := (s:OKState) => Bytecode.Dup(s, 9),
        Opcode.DUP10 := (s:OKState) => Bytecode.Dup(s, 10),
        Opcode.DUP11 := (s:OKState) => Bytecode.Dup(s, 11),
        Opcode.DUP12 := (s:OKState) => Bytecode.Dup(s, 12),
        Opcode.DUP13 := (s:OKState) => Bytecode.Dup(s, 13),
        Opcode.DUP14 := (s:OKState) => Bytecode.Dup(s, 14),
        Opcode.DUP15 := (s:OKState) => Bytecode.Dup(s, 15),
        Opcode.DUP16 := (s:OKState) => Bytecode.Dup(s, 16),
        // 0x90s: Exchange operations
        Opcode.SWAP1 := (s:OKState) => Bytecode.Swap(s, 1),
        Opcode.SWAP2 := (s:OKState) => Bytecode.Swap(s, 2),
        Opcode.SWAP3 := (s:OKState) => Bytecode.Swap(s, 3),
        Opcode.SWAP4 := (s:OKState) => Bytecode.Swap(s, 4),
        Opcode.SWAP5 := (s:OKState) => Bytecode.Swap(s, 5),
        Opcode.SWAP6 := (s:OKState) => Bytecode.Swap(s, 6),
        Opcode.SWAP7 := (s:OKState) => Bytecode.Swap(s, 7),
        Opcode.SWAP8 := (s:OKState) => Bytecode.Swap(s, 8),
        Opcode.SWAP9 := (s:OKState) => Bytecode.Swap(s, 9),
        Opcode.SWAP10 := (s:OKState) => Bytecode.Swap(s, 10),
        Opcode.SWAP11 := (s:OKState) => Bytecode.Swap(s, 11),
        Opcode.SWAP12 := (s:OKState) => Bytecode.Swap(s, 12),
        Opcode.SWAP13 := (s:OKState) => Bytecode.Swap(s, 13),
        Opcode.SWAP14 := (s:OKState) => Bytecode.Swap(s, 14),
        Opcode.SWAP15 := (s:OKState) => Bytecode.Swap(s, 15),
        Opcode.SWAP16 := (s:OKState) => Bytecode.Swap(s, 16),
        // 0xA0s: Log operations
        // else if LOG0 <=opcode <= LOG4 := (s:OKState)
         //   var k := opcode - LOG0) as int; evalLOG(st,k),
        // 0xf0
        //  CREATE := (s:OKState) => Bytecode.evalCREATE(s),
        //  CALL := (s:OKState) => Bytecode.evalCALL(s),
        //  CALLCODE := (s:OKState) => Bytecode.evalCALLCODE(s),
        Opcode.RETURN := (s:OKState) => Bytecode.Return(s),
        // DELEGATECALL := (s:OKState) => Bytecode.evalDELEGATECALL(s),
        // CREATE2 := (s:OKState) => Bytecode.evalCREATE2(s),
        // STATICCALL := (s:OKState) => Bytecode.evalSTATICCALL(s),
        Opcode.REVERT := (s:OKState) => Bytecode.Revert(s)
        // SELFDESTRUCT := (s:OKState) => Bytecode.evalSELFDESTRUCT(s),
    ]

    // A little helper method
    function method Push(s: OKState, k: nat) : State
    requires k > 0 && k <= 32 {
        if s.CodeOperands() >= k
        then
            var bytes := Code.Slice(s.evm.code, (s.evm.pc+1), k);
            assert 0 < |bytes| && |bytes| <= 32;
            Bytecode.Push(s,bytes)
        else
            State.INVALID
    }
}
