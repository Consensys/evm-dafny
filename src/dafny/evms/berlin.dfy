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

    /** The gas cost of opcodes.
     *
     *  @param op   The opcode to look up.
     *  @returns    The gas cost function that corresponds to the opcode 
     *              or `None` if no defined/implemented.
     */
    function method OpGas(op: u8): Option<OKState -> nat> {
        Gas.GasOne(op)
    }

    /** The semantics of opcodes.
     *
     *  @param op   The opcode to look up.
     *  @returns    The state transformer that corresponds to the opcode 
     *              or `None` if no defined/implemented.
     */
    function method OpSem(op: u8): Option<OKState -> State> 
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
            case MSIZE => Some((s:OKState) => Bytecode.MSize(s))
            case JUMPDEST =>  Some((s:OKState) => Bytecode.JumpDest(s))
            // 0x60s & 0x70s: Push operations
            case PUSH1 =>  Some((s: OKState) => Push(s,1))
            case PUSH2 =>  Some((s: OKState) => Push(s,2))
            case PUSH3 =>  Some((s: OKState) => Push(s,3))
            case PUSH4 =>  Some((s: OKState) => Push(s,4))
            case PUSH5 =>  Some((s: OKState) => Push(s,5))
            case PUSH6 =>  Some((s: OKState) => Push(s,6))
            case PUSH7 =>  Some((s: OKState) => Push(s,7))
            case PUSH8 =>  Some((s: OKState) => Push(s,8))
            case PUSH9 =>  Some((s: OKState) => Push(s,9))
            case PUSH10 =>  Some((s: OKState) => Push(s,10))
            case PUSH11 =>  Some((s: OKState) => Push(s,11))
            case PUSH12 =>  Some((s: OKState) => Push(s,12))
            case PUSH13 =>  Some((s: OKState) => Push(s,13))
            case PUSH14 =>  Some((s: OKState) => Push(s,14))
            case PUSH15 =>  Some((s: OKState) => Push(s,15))
            case PUSH16 =>  Some((s: OKState) => Push(s,16))
            case PUSH17 =>  Some((s: OKState) => Push(s,17))
            case PUSH18 =>  Some((s: OKState) => Push(s,18))
            case PUSH19 =>  Some((s: OKState) => Push(s,19))
            case PUSH20 =>  Some((s: OKState) => Push(s,20))
            case PUSH21 =>  Some((s: OKState) => Push(s,21))
            case PUSH22 =>  Some((s: OKState) => Push(s,22))
            case PUSH23 =>  Some((s: OKState) => Push(s,23))
            case PUSH24 =>  Some((s: OKState) => Push(s,24))
            case PUSH25 =>  Some((s: OKState) => Push(s,25))
            case PUSH26 =>  Some((s: OKState) => Push(s,26))
            case PUSH27 =>  Some((s: OKState) => Push(s,27))
            case PUSH28 =>  Some((s: OKState) => Push(s,28))
            case PUSH29 =>  Some((s: OKState) => Push(s,29))
            case PUSH30 =>  Some((s: OKState) => Push(s,30))
            case PUSH31 =>  Some((s: OKState) => Push(s,31))
            case PUSH32 =>  Some((s: OKState) => Push(s,32))
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
            case REVERT =>  Some((s:OKState) => Bytecode.Revert(s))
            // SELFDESTRUCT := Some((s:OKState) => Bytecode.evalSELFDESTRUCT(s),)
            case _ => None
    }

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
