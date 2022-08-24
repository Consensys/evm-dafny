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
include "util/memory.dfy"
include "util/bytes.dfy"
include "util/code.dfy"
include "util/context.dfy"
include "bytecode.dfy"

module Gas {
	import opened Opcode
	import opened EvmState
    import opened Int
    import opened ExtraTypes
    import opened Memory
    import opened Bytes
    import opened Code
    import opened Context
    import opened Bytecode

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

    /**
     *  Assign a cost as a function of the memory size.
     *
     *  @param  memUsedSize     The size of the memory in 32bytes (words).
     *  @returns                The cost of using a memory of size `memUsedSize`
     *  @note                   The memory cost is linear up to a certain point (
     *                          22*32 = 704 bytes), and then quadratic.
     */
    function method QuadraticCost(memUsedSize: nat): nat
    {
        G_MEMORY * memUsedSize + ((memUsedSize * memUsedSize) / 512)
    }

    /**
     *  The quadratic cost function is increasing.
     */
    lemma QuadraticCostIsMonotonic(x: nat, y: nat)
        ensures x >= y ==> QuadraticCost(x) >= QuadraticCost(y)
    {
        if x >= y {
            calc >= {
                G_MEMORY * x + ((x * x) / 512);
                G_MEMORY * y + ((y * y) / 512);
            }
        }
    }

    /*  Compute the cost of a memory expansion by an arbitrary number of words to cover a given address and data of length len.
     *  
     *  @param   mem         the current memory (also referred to as old memory)
     *  @param   address     the offs to start storing from
     *  @param   len         the length of data to read or write in bytes 
     *
     * @note                this implements the gas cost encountered upon memory expansion
     *                      if no expansion was necessary, no expansion cost would apply
     */
    function method ComputeDynGas(mem: Memory.T, address: nat, len: nat) : nat 
    {   
        if address + len - 1 < |mem.contents| then 
            0
        else 
            var before := |mem.contents| / 32;
            var after := Memory.SmallestLarg32(address + len - 1) / 32;
            QuadraticCostIsMonotonic(after, before);
            assert QuadraticCost(after) >= QuadraticCost(before);
            QuadraticCost(after) - QuadraticCost(before)
    } 

    /*  Compute the cost of a memory expansion by one word to cover a given address.
     *  
     *  @param   mem         the current memory (also referred to as old memory)
     *  @param   address     the offs to start storing from
     *
     * @note                this implements the gas cost encountered upon memory expansion
     *                      in which case no expansion cost is encountered
     */
    function method ComputeDynGasMSTORE(mem: Memory.T, address: nat) : nat
    {
        if address + 31 < |mem.contents| then
            0
        else
            var before := |mem.contents| / 32;
            var after := Memory.SmallestLarg32(address + 31) / 32;
            QuadraticCostIsMonotonic(after, before);
            assert QuadraticCost(after) >= QuadraticCost(before);
            QuadraticCost(after) - QuadraticCost(before)
    }

    /* compute the gas cost of memory expansion. Consider corner cases where exceptions
     * may have happened due to accessing maximum allowed memory, or underflowing the stack
     */
    function method GasCostMSTORE(st: State) : State
        requires !st.IsFailure()
    {
        /* check for the stack underflow */
        if st.Operands() >= 1
        then
            /* get the address which is the starting memory slot for storing the value in the memory*/
            var loc := st.Peek(0) as nat;
            /* check if storing a word in the memory, starting from the offset loc, exceeds the maximum accessible
             * memory size */
            if (loc + 31) < MAX_U256
                then
                /* compute if memory expansion is needed, and return the cost of the potential expansion */
                var costMemExpansion := ComputeDynGas(st.evm.memory, loc as nat, 32);
                /* check if there is enough gas available to cover the expansion costs */
                if costMemExpansion + G_VERYLOW <= st.Gas() 
                    then 
                        st.UseGas(costMemExpansion + G_VERYLOW)
                /* return an invalid state if there was not enough gas to pay for the memory expansion */
                else State.INVALID(INSUFFICIENT_GAS)
            else
                if G_VERYLOW <= st.Gas()
                    then
                        /* charge the constant gas amount, even if maximum accessible memory was encountered */
                        st.UseGas(G_VERYLOW)
                else    
                    State.INVALID(INSUFFICIENT_GAS)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    function method GasCostMLOAD(st: State) : State
        requires !st.IsFailure()
        ensures
            (Stack.Size(st.GetStack()) >= 1 && st.Peek(0) as nat + 31 < MAX_U256)
                <==>
            !MLoad(st).IsFailure()
        ensures st.IsFailure() ==> MLoad(st).IsFailure()
    {
        //
        if st.Operands() >= 1
        then
            var loc := st.Peek(0) as nat;
            // NOTE: This condition is not specified in the yellow paper.
            // It is not clear whether that was intended or not.  However, it is
            // impossible to trigger this in practice (due to the gas costs
            // involved).
            if loc + 31 < MAX_U256
            then
                /* compute if memory expansion is needed, and return the cost of the potential expansion */
                var costMemExpansion := ComputeDynGas(st.evm.memory, loc as nat, 32);
                /* check if there is enough gas available to cover the expansion costs */
                if costMemExpansion + G_VERYLOW <= st.Gas()
                    then
                        st.UseGas(costMemExpansion + G_VERYLOW)
                /* return an invalid state if there was not enough gas to pay for the memory expansion */
                else State.INVALID(INSUFFICIENT_GAS)
            else
                if G_VERYLOW <= st.Gas()
                    then
                        /* charge the constant gas amount, even if maximum accessible memory was encountered */
                        st.UseGas(G_VERYLOW)
                else
                    State.INVALID(INSUFFICIENT_GAS)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    function method gasCostRETURN(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            // Determine amount of data to return.
            var len := st.Peek(1) as nat;
            var start := st.Peek(0) as nat;
            // Sanity check bounds
            if (start+len) < MAX_U256
            then
                // Read out that data.
                var data := Memory.Slice(st.evm.memory, start, len);
                assert |data| == len;
                /* if the  length of data to read and return is zero, no gas charges apply 
                 * note that we do not need caring if the starting slot of reading data exceeds the maximum memory used
                 */
                if len == 0
                    then st.UseGas(G_ZERO)
                else
                /* if the length of data is greater than zero, check for possible expansions needed and apply the charges */
                var costMemExpansion := ComputeDynGas(st.evm.memory, start, len);
                if costMemExpansion <= st.Gas()
                    then
                        st.UseGas(G_ZERO + costMemExpansion)
                else
                    State.INVALID(INSUFFICIENT_GAS)
            else
                st.UseGas(G_ZERO)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    function method gasCostREVERT(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            // Determine amount of data to return.
            var len := st.Peek(1) as nat;
            var start := st.Peek(0) as nat;
            // Sanity check bounds
            if (start+len) < MAX_U256
            then
                // Read out that data.
                var data := Memory.Slice(st.evm.memory, start, len);
                assert |data| == len;
                /* if the  length of data to read and revert on is zero, no gas charges apply 
                 * note that we do not need caring if the starting slot of reading data exceeds the maximum memory used
                 */
                if len == 0
                    then st.UseGas(G_ZERO)
                else
                /* if the length of data is greater than zero, check for possible expansions needed and apply the charges */
                var costMemExpansion := ComputeDynGas(st.evm.memory, start, len);
                if costMemExpansion <= st.Gas()
                    then
                        st.UseGas(G_ZERO + costMemExpansion)
                else
                    State.INVALID(INSUFFICIENT_GAS)
            else
                st.UseGas(G_ZERO)
        else
            State.INVALID(STACK_UNDERFLOW)
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
            case MLOAD => GasCostMLOAD(s)
            case MSTORE => GasCostMSTORE(s)
            case MSTORE8 => s.UseGas(G_VERYLOW)
            case SLOAD => s.UseGas(G_HIGH) // for now
            case SSTORE => s.UseGas(G_HIGH) // for now
            case JUMP => s.UseGas(G_MID)
            case JUMPI => s.UseGas(1) // for now
            case PC => s.UseGas(G_BASE)
            case MSIZE => s.UseGas(G_BASE)
            case GAS => s.UseGas(G_BASE)
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
            case CALL => s.UseGas(G_CALLSTIPEND) // for now
            // CALLCODE => s.UseGas(1)
            case RETURN => s.UseGas(G_ZERO)
            // DELEGATECALL => s.UseGas(1)
            // CREATE2 => s.UseGas(1)
            // STATICCALL => s.UseGas(1)
            case REVERT => s.UseGas(G_ZERO)
            case SELFDESTRUCT => s.UseGas(1)
            case _ => State.INVALID(INVALID_OPCODE)
    }
}
