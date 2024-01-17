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
include "../../libs/DafnyCrypto/src/dafny/util/option.dfy"
include "bytecode.dfy"
include "core/fork.dfy"
include "state.dfy"
include "opcodes.dfy"
include "gas.dfy"

/**
 * Top-level definition of an Ethereum Virtual Machine.
 */
module EVM {
    import opened EvmState
    import opened Gas
    import opened Int
    import opened EvmFork
    import opened Opcode
    import opened Optional
    import Bytecode

    /** An empty VM, with some initial gas and initial stack.
     *
     *  @param  gas     The gas loaded in this EVM.
     *  @returns        An ready-to-use EVM.
     */
    function Init(gas: nat, fork : Fork := BERLIN, stk: seq<u256> := [], code: seq<u8> := []) : (st:ExecutingState)
    requires |code| <= Code.MAX_CODE_SIZE
    requires |stk| <= 1024
    {
        var tx := Context.Create(0,0,0,0,[],true,0,Context.Block.Info(0,0,0,0,0,0,0));
        Create(fork, tx, map[0:=WorldState.DefaultAccount()], gas, code, Precompiled.DEFAULT, stk)
    }

    /**
     * Create a fresh EVM to execute a given sequence of bytecode instructions.
     * The EVM is initialised with an empty stack and empty local memory.
     */
    function Create(fork: Fork, context: Context.T, world: map<u160,WorldState.Account>, gas: nat, code: seq<u8>, precompiled: Precompiled.T := Precompiled.DEFAULT, st: seq<u256> := []) : ExecutingState
    // Code to executed cannot exceed maximum limit.
    requires |code| <= Code.MAX_CODE_SIZE
    requires |st| <= Stack.CAPACITY
    // Account under which EVM is executing must exist!
    requires context.address in world {
        var stck := Stack.Make(st);
        var mem := Memory.Create();
        var wld := WorldState.Create(world);
        var cod := Code.Create(code);
        var sub := SubState.Create();
        var evm := EVM(fork,stack:=stck,memory:=mem,world:=wld,context:=context,precompiled:=precompiled,code:=cod,substate:=sub,gas:=gas,pc:=0);
        // Off we go!
        EXECUTING(evm)
    }

    /**
     * Execute the next bytecode as determined by the current machine's state.
     * This requires decoding the bytecode at the current PC location.
     */
    function Execute(st: ExecutingState): State {
        // Read opcode byte from memory.  If the read is out-of-bounds, then
        // STOP is returned by default.
        var opcode := Code.DecodeUint8(st.evm.code,st.evm.pc as nat);
        // Check fork supports given bytecode
        if st.evm.fork.IsBytecode(opcode)
        then
            // Deduct gas for the given bytecode.
            match DeductGas(opcode,st)
                // Not out of gas
                case EXECUTING(vm) => ExecuteBytecode(opcode,EXECUTING(vm))
                // Out of gas (or invalid opcode)
                case s => s
        else
            ERROR(INVALID_OPCODE)
    }

    /**
     *  Execute the next instruction
     *  return
     *  @note       If the opcode semantics/gas is not implemented, the next
     *              state is INVALID.
     */
    function {:tailrecursion true} ExecuteN(st:ExecutingState, steps: nat := 1): State
    decreases steps
    requires steps > 0
    {
        // Execute next instruction
        var nst := Execute(st);
        // Recurse as necessary
        if steps == 1 || !nst.EXECUTING? then nst else ExecuteN(nst,steps-1)
    }

    /**
     * Deduct gas for the given opcode from the executing state.  This may or
     * may not result in an executing state.  For example, if the executing
     * state does not have enough gas.
     */
    function DeductGas(op: u8, s: ExecutingState): State
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
            case EXP => s.UseGas(CostExp(s))
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
            case KECCAK256 => s.UseGas(CostExpandRange(s,2,0,1) + CostKeccak256(s))
            // 0x30s: Environment Information
            case ADDRESS => s.UseGas(G_BASE)
            case BALANCE => s.UseGas(CostExtAccount(s))
            case ORIGIN => s.UseGas(G_BASE)
            case CALLER => s.UseGas(G_BASE)
            case CALLVALUE => s.UseGas(G_BASE)
            case CALLDATALOAD => s.UseGas(G_VERYLOW)
            case CALLDATASIZE => s.UseGas(G_BASE)
            case CALLDATACOPY => s.UseGas(CostExpandRange(s,3,0,2) + G_VERYLOW + CostCopy(s,2))
            case CODESIZE => s.UseGas(G_BASE)
            case CODECOPY => s.UseGas(CostExpandRange(s,3,0,2) + G_VERYLOW + CostCopy(s,2))
            case GASPRICE => s.UseGas(G_BASE)
            case EXTCODESIZE => s.UseGas(CostExtAccount(s))
            case EXTCODECOPY => s.UseGas(CostExpandRange(s,4,1,3) + CostExtAccount(s) + CostCopy(s,3))
            case RETURNDATASIZE => s.UseGas(G_BASE)
            case RETURNDATACOPY => s.UseGas(CostExpandRange(s,3,0,2) + G_VERYLOW + CostCopy(s,2))
            case EXTCODEHASH => s.UseGas(CostExtAccount(s))
            // 0x40s: Block Information
            case BLOCKHASH => s.UseGas(G_BLOCKHASH)
            case COINBASE => s.UseGas(G_BASE)
            case TIMESTAMP => s.UseGas(G_BASE)
            case NUMBER => s.UseGas(G_BASE)
            case DIFFICULTY => s.UseGas(G_BASE)
            case GASLIMIT => s.UseGas(G_BASE)
            case CHAINID => s.UseGas(G_BASE)
            case SELFBALANCE => s.UseGas(G_LOW)
            case BASEFEE => s.UseGas(G_BASE)
            // 0x50s: Stack, Memory, Storage and Flow
            case POP => s.UseGas(G_BASE)
            case MLOAD => s.UseGas(CostExpandBytes(s,1,0,32) + G_VERYLOW)
            case MSTORE => s.UseGas(CostExpandBytes(s,2,0,32) + G_VERYLOW)
            case MSTORE8 => s.UseGas(CostExpandBytes(s,2,0,1) + G_VERYLOW)
            case SLOAD => s.UseGas(CostSLoad(s))
            case SSTORE => s.UseGas(CostSStore(s)) // for now
            case JUMP => s.UseGas(G_MID)
            case JUMPI => s.UseGas(G_HIGH) // for now
            case PC => s.UseGas(G_BASE)
            case MSIZE => s.UseGas(G_BASE)
            case GAS => s.UseGas(G_BASE)
            case JUMPDEST => s.UseGas(G_JUMPDEST)
            case MCOPY => s.UseGas(CostExpandDoubleRange(s,3,0,2,1,2) + G_VERYLOW + CostCopy(s,2))
            case PUSH0 => s.UseGas(G_BASE)
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
            case LOG0 => s.UseGas(CostExpandRange(s,2,0,1) + CostLog(s,0))
            case LOG1 => s.UseGas(CostExpandRange(s,3,0,1) + CostLog(s,1))
            case LOG2 => s.UseGas(CostExpandRange(s,4,0,1) + CostLog(s,2))
            case LOG3 => s.UseGas(CostExpandRange(s,5,0,1) + CostLog(s,3))
            case LOG4 => s.UseGas(CostExpandRange(s,6,0,1) + CostLog(s,4))
            // 0xf0
            case CREATE => s.UseGas(CostExpandRange(s,3,1,2) + CostCreate(s))
            case CALL => s.UseGas(CostExpandDoubleRange(s,7,3,4,5,6) + CallCost(s))
            case CALLCODE => s.UseGas(CostExpandDoubleRange(s,7,3,4,5,6) + CallCodeCost(s))
            case RETURN => s.UseGas(CostExpandRange(s,2,0,1) + G_ZERO)
            case DELEGATECALL => s.UseGas(CostExpandDoubleRange(s,6,2,3,4,5) + DelegateCallCost(s))
            case CREATE2 => s.UseGas(CostExpandRange(s,4,1,2) + CostCreate2(s))
            case STATICCALL => s.UseGas(CostExpandDoubleRange(s,6,2,3,4,5) + StaticCallCost(s))
            case REVERT => s.UseGas(CostExpandRange(s,2,0,1) + G_ZERO)
            case SELFDESTRUCT => s.UseGas(CostSelfDestruct(s))
            case _ => ERROR(INVALID_OPCODE)
    }

    /**
     * Execute a given bytecode from the executing state.  This assumes gas has
     * already been deducted.  Again, this may or may not result in an executing
     * state, depending on whether the necessary conditions for execution were
     * met.  For example, executing an instruction (e.g. ADD) which requires
     * operands on the stack when there are no operands on the stack will result
     * in an error state.
     */
    function ExecuteBytecode(op: u8, st: ExecutingState): State {
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
            case BASEFEE => Bytecode.BaseFee(st)
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
            case MCOPY => Bytecode.MCopy(st)
            case PUSH0 => Bytecode.Push0(st)
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
