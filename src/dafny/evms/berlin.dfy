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

module EvmBerlin refines EVM {
    import opened Int 
    import Opcode
    import Bytecode

    /**
     * Create a fresh EVM to execute a given sequence of bytecode instructions.
     * The EVM is initialised with an empty stack and empty local memory.
     */
    function method Create(context: Context.T, storage: map<u256,u256>, gas: nat, code: seq<u8>) : State
    requires |code| <= Code.MAX_CODE_SIZE {
        var stck := Stack.Create();
        var mem := Memory.Create();
        var sto := Storage.Create(storage);
        var cod := Code.Create(code);
        var evm := EVM(stack:=stck,memory:=mem,storage:=sto,context:=context,code:=cod,gas:=gas,pc:=0);
        // Off we go!
        State.OK(evm)
    }

    /**
    * Execute a single step of the EVM.  This either States in a valid EVM (i.e. so execution
    * can continue), or some form of halt (e.g. exceptional, revert, etc).
    */
    function method Execute(st:State) : State {
        var OK(vm) := st;
        // Decode
        var opcode := st.Decode();
        // 0x00s: STOP & Arithmetic
        if opcode == Opcode.STOP then Bytecode.Stop(st)
        else if opcode == Opcode.ADD then Bytecode.Add(st)
        else if opcode == Opcode.MUL then Bytecode.Mul(st)
        else if opcode == Opcode.SUB then Bytecode.Sub(st)
        else if opcode == Opcode.DIV then Bytecode.Div(st)
        else if opcode == Opcode.SDIV then Bytecode.SDiv(st)
        else if opcode == Opcode.MOD then Bytecode.Mod(st)
        else if opcode == Opcode.SMOD then Bytecode.SMod(st)
        else if opcode == Opcode.ADDMOD then Bytecode.AddMod(st)
        else if opcode == Opcode.MULMOD then Bytecode.MulMod(st)
        // else if opcode == EXP then Bytecode.evalEXP(st)
        // else if opcode == SIGNEXTEND then Bytecode.evalSIGNEXTEND(st)
        // 0x10s: Comparison & Bitwise Logic
        else if opcode == Opcode.LT then Bytecode.Lt(st)
        else if opcode == Opcode.GT then Bytecode.Gt(st)
        else if opcode == Opcode.SLT then Bytecode.SLt(st)
        else if opcode == Opcode.SGT then Bytecode.SGt(st)
        else if opcode == Opcode.EQ then Bytecode.Eq(st)
        else if opcode == Opcode.ISZERO then Bytecode.IsZero(st)
        else if opcode == Opcode.AND then Bytecode.And(st)
        else if opcode == Opcode.OR then Bytecode.Or(st)
        else if opcode == Opcode.XOR then Bytecode.Xor(st)
        else if opcode == Opcode.NOT then Bytecode.Not(st)
        else if opcode == Opcode.BYTE then Bytecode.Byte(st)
        else if opcode == Opcode.SHL then Bytecode.Shl(st)
        else if opcode == Opcode.SHR then Bytecode.Shr(st)
        // else if opcode == SAR then Bytecode.evalSAR(st)
        // 0x20s
        // else if opcode == KECCAK256 then Bytecode.evalKECCAK256(st)
        // 0x30s: Environment Information
        // else if opcode == ADDRESS then Bytecode.evalADDRESS(st)
        // else if opcode == BALANCE then Bytecode.evalBALANCE(st)
        // else if opcode == ORIGIN then Bytecode.evalORIGIN(st)
        // else if opcode == CALLER then Bytecode.evalCALLER(st)
        // else if opcode == CALLVALUE then Bytecode.evalCALLVALUE(st)
        else if opcode == Opcode.CALLDATALOAD then Bytecode.CallDataLoad(st)
        else if opcode == Opcode.CALLDATASIZE then Bytecode.CallDataSize(st)
        else if opcode == Opcode.CALLDATACOPY then Bytecode.CallDataCopy(st)
        // else if opcode == CODESIZE then Bytecode.evalCODESIZE(st)
        // else if opcode == CODECOPY then Bytecode.evalCODECOPY(st)
        // else if opcode == GASPRICE then Bytecode.evalGASPRICE(st)
        // else if opcode == EXTCODESIZE then Bytecode.evalEXTCODESIZE(st)
        // else if opcode == EXTCODECOPY then Bytecode.evalEXTCODECOPY(st)
        // else if opcode == RETURNDATASIZE then Bytecode.evalRETURNDATASIZE(st)
        // else if opcode == RETURNDATACOPY then Bytecode.evalRETURNDATACOPY(st)
        // else if opcode == EXTCODEHASH then Bytecode.evalEXTCODEHASH(st)
        // 0x40s: Block Information
        // else if opcode == BLOCKHASH then Bytecode.evalBLOCKHASH(st)
        // else if opcode == COINBASE then Bytecode.evalCOINBASE(st)
        // else if opcode == TIMESTAMP then Bytecode.evalTIMESTAMP(st)
        // else if opcode == NUMBER then Bytecode.evalNUMBER(st)
        // else if opcode == DIFFICULTY then Bytecode.evalDIFFICULTY(st)
        // else if opcode == GASLIMIT then Bytecode.evalGASLIMIT(st)
        // else if opcode == CHAINID then Bytecode.evalCHAINID(st)
        // else if opcode == SELFBALANCE then Bytecode.evalSELFBALANCE(st)
        // 0x50s: Stack, Memory, Storage and Flow
        else if opcode == Opcode.POP then Bytecode.Pop(st)
        else if opcode == Opcode.MLOAD then Bytecode.MLoad(st)
        else if opcode == Opcode.MSTORE then Bytecode.MStore(st)
        else if opcode == Opcode.MSTORE8 then Bytecode.MStore8(st)
        else if opcode == Opcode.SLOAD then Bytecode.SLoad(st)
        else if opcode == Opcode.SSTORE then Bytecode.SStore(st)
        else if opcode == Opcode.JUMP then Bytecode.Jump(st)
        else if opcode == Opcode.JUMPI then Bytecode.JumpI(st)
        else if opcode == Opcode.PC then Bytecode.Pc(st)
        else if opcode == Opcode.JUMPDEST then Bytecode.JumpDest(st)
        // 0x60s & 0x70s: Push operations
        else if opcode == Opcode.PUSH1 && st.CodeOperands() >= 1 then
            var k := Code.DecodeUint8(vm.code, (vm.pc + 1) as nat);
            Bytecode.Push1(st, k)
        else if opcode == Opcode.PUSH2 && st.CodeOperands() >= 2 then
            var k := Code.DecodeUint16(vm.code, (vm.pc + 1) as nat);
            Bytecode.Push2(st, k)
        // 0x80s: Duplicate operations
        else if Opcode.DUP1 <= opcode <= Opcode.DUP16 then
            var k := (opcode - Opcode.DUP1) as int; Bytecode.Dup(st,k+1)
        // 0x90s: Exchange operations
        else if Opcode.SWAP1 <= opcode <= Opcode.SWAP16 then
            var k := (opcode - Opcode.SWAP1) as int; Bytecode.Swap(st,k+1)
        // 0xA0s: Log operations
        // else if LOG0 <= opcode <= LOG4 then
        //   var k := (opcode - LOG0) as int; evalLOG(st,k)
        // 0xf0
        // else if opcode == CREATE then Bytecode.evalCREATE(st)
        // else if opcode == CALL then Bytecode.evalCALL(st)
        // else if opcode == CALLCODE then Bytecode.evalCALLCODE(st)
        else if opcode == Opcode.RETURN then Bytecode.Return(st)
        //else if opcode == DELEGATECALL then Bytecode.evalDELEGATECALL(st)
        //else if opcode == CREATE2 then Bytecode.evalCREATE2(st)
        //else if opcode == STATICCALL then Bytecode.evalSTATICCALL(st)
        else if opcode == Opcode.REVERT then Bytecode.Revert(st)
        //else if opcode == SELFDESTRUCT then Bytecode.evalSELFDESTRUCT(st)
        else
        // Invalid opcode
        State.INVALID
    }
}
