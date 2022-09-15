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
include "state.dfy"
include "gas.dfy"

module Bytecode {
    import opened Int
    import U256
    import I256
    import Word
    import Bytes
    import External
    import GasCalc = Gas
    import opened EvmState
    import opened ExtraTypes

    // =====================================================================
    // 0s: Stop and Arithmetic Operations
    // =====================================================================

    /**
     * Evaluate the STOP bytecode.  This halts the machine without
     * return output data.
     */
    function method Stop(st: State) : State
    requires !st.IsFailure() {
        State.RETURNS(gas:=st.Gas(),data:=[],world:=st.evm.world,substate:=st.evm.substate)
    }

    /**
    * Unsigned integer addition with modulo arithmetic.
    */
    function method Add(st: State) : State
    requires !st.IsFailure() {
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var res := (lhs + rhs) % TWO_256;
            st.Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Unsigned integer multiplication with modulo arithmetic.
    */
    function method Mul(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var res := (lhs * rhs) % TWO_256;
            st.Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Unsigned integer subtraction with modulo arithmetic.
    */
    function method Sub(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var res := (lhs - rhs) % TWO_256;
            st.Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    // =============================================================================
    // Helpers
    // =============================================================================

    /**
    * Unsigned integer division with handling for zero.
    */
    function method DivWithZero(lhs:u256, rhs:u256) : u256 {
        if rhs == 0 then 0 as u256
        else
        (lhs / rhs) as u256
    }

    /**
    * Unsigned integer remainder with handling for zero.
    */
    function method ModWithZero(lhs:u256, rhs:u256) : u256 {
        if rhs == 0 then 0 as u256
        else
        (lhs % rhs) as u256
    }

    /**
    * Signed integer division with handling for zero and overflow.
    * A key challenge here is that, in Dafny, division is Euclidean
    * (i.e. rounds down).  In contrast, division on the EVM is
    * non-Euclidean (i.e. rounds towards zero).  This means we cannot
    * use Dafny's division operator as is for implementing SDIV
    * (though for DIV it is OK).  Instead, we have to explicitly
    * manage the cases for negative operands.
    */
    function method SDivWithZero(lhs:i256, rhs:i256) : i256 {
        if rhs == 0 then 0 as i256
        else if rhs == -1 && lhs == (-TWO_255 as i256)
        then
        -TWO_255 as i256
        else
        // Do not use Dafny's division operator here!
        I256.div(lhs,rhs)
    }

    /**
    * Signed integer remainder with handling for zero.
    * A key challenge here is that, in Dafny, division is Euclidean
    * (i.e. rounds down).  In contrast, division on the EVM is
    * non-Euclidean (i.e. rounds towards zero).  This means we cannot
    * use Dafny's remainder operator as is for implementing SMOD
    * (though for MOD it is OK).  Instead, we have to explicitly
    * manage the cases for negative operands.
    */
    function method SModWithZero(lhs:i256, rhs:i256) : i256 {
        if rhs == 0 then 0 as i256
        else
        // Do not use Dafny's remainder operator here!
        I256.Rem(lhs,rhs)
    }


    /**
    * Unsigned integer division.
    */
    function method Div(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1);
            var res := DivWithZero(lhs,rhs) as u256;
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Signed integer division.
    */
    function method SDiv(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := Word.asI256(st.Peek(0));
            var rhs := Word.asI256(st.Peek(1));
            var res := Word.fromI256(SDivWithZero(lhs,rhs));
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * (Unsigned) Modulo remainder.
    */
    function method Mod(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1);
            var res := ModWithZero(lhs,rhs) as u256;
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Signed integer remainder:
    */
    function method SMod(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := Word.asI256(st.Peek(0));
            var rhs := Word.asI256(st.Peek(1));
            var res := Word.fromI256(SModWithZero(lhs,rhs));
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Unsigned integer modulo addition.
    */
    function method AddMod(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 3
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var rem := st.Peek(2) as int;
            var res := if rem == 0 then 0 else(lhs + rhs) % rem;
            st.Pop().Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Unsigned integer modulo multiplication.
     */
    function method MulMod(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 3
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var rem := st.Peek(2) as int;
            var res := if rem == 0 then 0 else(lhs * rhs) % rem;
            st.Pop().Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Exponential operation
     */
    function method Exp(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var base := st.Peek(0) as int;
            var power := st.Peek(1) as int;
            var res := Int.Pow(base,power) % TWO_256;
            st.Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Extend length of two's complement signed integer.
     */
    function method SignExtend(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var width := st.Peek(0);
            var item := st.Peek(1);
            var res := U256.SignExtend(item,width as nat);
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 10s: Comparison & Bitwise Logic Operations
    // =====================================================================

    /**
    * (Unsigned) less-than comparison.
    */
    function method Lt(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1);
            if lhs < rhs
                then
                st.Pop().Pop().Push(1).Next()
            else
                st.Pop().Pop().Push(0).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * (Unsigned) greater-than comparison.
    */
    function method Gt(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1);
            if lhs > rhs
                then
                st.Pop().Pop().Push(1).Next()
            else
                st.Pop().Pop().Push(0).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Signed less-than comparison.
    */
    function method SLt(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := Word.asI256(st.Peek(0));
            var rhs := Word.asI256(st.Peek(1));
            if lhs < rhs
                then
                st.Pop().Pop().Push(1).Next()
            else
                st.Pop().Pop().Push(0).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Signed greater-than comparison.
    */
    function method SGt(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := Word.asI256(st.Peek(0));
            var rhs := Word.asI256(st.Peek(1));
            if lhs > rhs
                then
                st.Pop().Pop().Push(1).Next()
            else
                st.Pop().Pop().Push(0).Next()
        else
                State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Equality comparison.
    */
    function method Eq(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
        var lhs := st.Peek(0);
        var rhs := st.Peek(1);
        if lhs == rhs
            then
            st.Pop().Pop().Push(1).Next()
        else
            st.Pop().Pop().Push(0).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Simple not operator.
    */
    function method IsZero(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 1
        then
            var mhs := st.Peek(0);
            if mhs == 0
                then
                st.Pop().Push(1).Next()
            else
                st.Pop().Push(0).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Bitwise AND operation.
    */
    function method And(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as bv256;
            var rhs := st.Peek(1) as bv256;
            var res := (lhs & rhs) as u256;
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Bitwise OR operation.
    */
    function method {:verify false} Or(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as bv256;
            var rhs := st.Peek(1) as bv256;
            var res := (lhs | rhs) as u256;
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Bitwise XOR operation.
    */
    function method {:verify false} Xor(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as bv256;
            var rhs := st.Peek(1) as bv256;
            var res := (lhs ^ rhs) as u256;
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Bitwise NOT operation.
    */
    function method Not(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 1
        then
            var mhs := st.Peek(0) as bv256;
            var res := (!mhs) as u256;
            st.Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Retrieve single byte from word.
    */
    function method Byte(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var val := st.Peek(1);
            var k := st.Peek(0) as nat;
            var res := if k < 32 then U256.NthUint8(val,k) else 0 as u8;
            st.Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Left shift operation.
     */
    function method Shl(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var rhs := st.Peek(0);
            var lhs := st.Peek(1);
            var res := U256.Shl(lhs,rhs);
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Right shift operation.
     */
    function method {:verify false} Shr(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var rhs := st.Peek(0);
            var lhs := st.Peek(1);
            var res := U256.Shr(lhs,rhs);
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Arithmetic (signed) right shift operation.
     */
    function method Sar(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var rhs := st.Peek(0);
            var lhs := Word.asI256(st.Peek(1));
            var res := I256.Sar(lhs,rhs);
            st.Pop().Pop().Push(res).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 20s: Keccak256
    // =====================================================================

    /**
     * Computer Keccak256 hash.
     */
    function method Keccak256(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var loc := st.Peek(0) as nat;
            var len := st.Peek(1) as nat;
            var bytes := Memory.Slice(st.evm.memory, loc, len);
            var hash := External.sha3(bytes);
            st.Expand(loc,len).Pop().Pop().Push(hash).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 30s: Environment Information
    // =====================================================================

    function method BlockHash(st: State) : State
    requires !st.IsFailure() {
        if st.Operands() >= 1
        then
            // FIXME: what to do here?
            var n := st.Peek(0);
            st.Pop().Push(0).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Get address of currently executing account.
     */
    function method Address(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.address as u256).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get balance of the given account.
     */
    function method Balance(st: State) : State
    requires !st.IsFailure() {
        if st.Operands() >= 1
        then
            // Determine account address
            var account := (st.Peek(0) as nat % TWO_160) as u160;
            // Get balance (or zero if no account exists)
            var balance := if st.evm.world.Exists(account)
                then st.evm.world.Balance(account) else 0;
            // Push balance!
            st.Pop().Push(balance).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get execution origination address.  This is the sender of the original
     * transaction; it is never an account with non-empty associated code.
     */
    function method Origin(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.origin as u256).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get caller address.
     */
    function method Caller(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.sender as u256).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get deposited value by the instruction/transaction responsible for
     * this execution.
     */
    function method CallValue(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.callValue).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
    * Get input data from the current environment.
    */
    function method CallDataLoad(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 1
        then
            var loc := st.Peek(0);
            var val := if loc >= st.evm.context.CallDataSize() then 0
                else st.evm.context.CallDataRead(loc);
            st.Pop().Push(val).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Get size of input data in current environment.
     */
    function method CallDataSize(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Capacity() >= 1
        then
            var len := st.evm.context.CallDataSize();
            st.Push(len).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     *  Copy input data in the current environment to memory.
     */
    function method CallDataCopy(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 3
        then
            var m_loc := st.Peek(0) as nat;
            var d_loc := st.Peek(1);
            var len := st.Peek(2) as nat;

            // NOTE: This condition is not specified in the yellow paper.
            // Its not clear whether that was intended or not.  However, its
            // impossible to trigger this in practice (due to the gas costs
            // involved).
            if m_loc + len < MAX_U256
            then
                // Slice bytes out of call data (with padding as needed)
                var data := st.evm.context.CallDataSlice(d_loc,len as nat);
                // Sanity check
                assert |data| == len;
                // Copy slice into memory
                st.Expand(m_loc as nat, len as nat).Pop().Pop().Pop().Copy(m_loc,data).Next()
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Get size of code running in current environment.
     */
    function method CodeSize(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Capacity() >= 1
        then
            st.Push(Code.Size(st.evm.code)).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Copy code running in current environment to memory.
     */
    function method CodeCopy(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 3
        then
            var m_loc := st.Peek(0) as nat;
            var d_loc := st.Peek(1) as nat;
            var len := st.Peek(2) as nat;
            var last := (m_loc as nat) + len;
            // NOTE: This condition is not specified in the yellow paper.
            // Its not clear whether that was intended or not.  However, its
            // impossible to trigger this in practice (due to the gas costs
            // involved).
            if last < MAX_U256
            then
                // Slice bytes out of code (with padding as needed)
                var data := Code.Slice(st.evm.code,d_loc,len);
                // Sanity check
                assert |data| == len;
                // Copy slice into memory
                st.Expand(m_loc as nat, len).Pop().Pop().Pop().Copy(m_loc,data).Next()
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Get price of gas in current environment.
     */
    function method GasPrice(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.gasPrice).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get size of return data from the previous call from the current
     * environment.
     */
    function method ReturnDataSize(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            var len := st.evm.context.ReturnDataSize();
            st.Push(len as u256).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     *  Copy return data from previous call to memory.
     */
    function method ReturnDataCopy(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 3
        then
            var m_loc := st.Peek(0) as nat;
            var d_loc := st.Peek(1) as nat;
            var len := st.Peek(2) as nat;
            if (d_loc + len) <= st.evm.context.ReturnDataSize()
            then
                // Slice bytes out of return data (with padding as needed)
                var data := st.evm.context.ReturnDataSlice(d_loc,len);
                // Sanity check
                assert |data| == len;
                // Copy slice into memory
                st.Expand(m_loc, len).Pop().Pop().Pop().Copy(m_loc,data).Next()
            else
                State.INVALID(RETURNDATA_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 40s: Block Information
    // =====================================================================

    /**
     * Get the current block's beneficiay address.
     */
    function method CoinBase(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.coinBase).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get the current block's timestamp.
     */
    function method TimeStamp(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.timeStamp).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get the current block's number.
     */
    function method Number(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.number).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get the current block's difficulty.
     */
    function method Difficulty(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.difficulty).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get the current block's gaslimit.
     */
    function method GasLimit(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.gasLimit).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get the chain ID.
     */
    function method ChainID(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.chainID).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get balance of currently executing account.
     */
    function method SelfBalance(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            // Get address of currently executing account
            var address := st.evm.context.address;
            // Get balance of said account
            var balance := st.evm.world.Balance(address);
            // Done
            st.Push(balance).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    // =====================================================================
    // 50s: Stack, Memory Storage and Flow Operations
    // =====================================================================

    /**
    * Pop word from stack.
    */
    function method Pop(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 1
        then
            st.Pop().Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Get the size of active memory in bytes.
     */
    function method MSize(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            var s := Memory.Size(st.evm.memory);
            if s <= MAX_U256
            then
                st.Push(s as u256).Next()
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     *  Read a word from memory.
     *
     *  @param  st  A state.
     *  @returns    A new state with:
     *              if some conditions are met (see spec):
     *              1. pop the top of stack
     *              2. push the value of the 32 bytes starting at memory[stack[0]]
     *              on top of the stack;
     *              3. the program counter advanced by one.
     *              and otherwise an invalid state.
     *
     *  @note       The memory may be expanded during this process, and this incurs
     *              some gas costs (charged separately).
     */
    function method MLoad(st: State) : State
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
                // Break out expanded state
                var nst := st.Expand(loc,32);
                // Read from expanded state
                nst.Pop().Push(nst.Read(loc)).Next()
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
        State.INVALID(STACK_UNDERFLOW)
    }

    /**
     *  Store a word into memory.
     *
     *  @param  st  A state.
     *  @returns    A new state with:
     *              if some conditions are met (see spec):
     *              1. stack[1] stored at stack[0] in memory,
     *              2. the two top elements of the stack popped,
     *              3. the program counter advanced by one.
     *              and otherwise an invalid state.
     *
     *  @note       The memory may be expanded during this process, and this incurs
     *              some gas costs (charged separately).
     */
    function method MStore(st: State) : State
        requires !st.IsFailure()
        ensures
            (Stack.Size(st.GetStack()) >= 2 && st.Peek(0) as nat + 31 < MAX_U256)
                <==>
            !MStore(st).IsFailure()
        ensures st.IsFailure() ==> MStore(st).IsFailure()
    {
        //
        if st.Operands() >= 2
        then
            var loc := st.Peek(0) as nat;
            var val := st.Peek(1);
            // NOTE: This condition is not specified in the yellow paper.
            // It is not clear whether that was intended or not.  However, it is
            // impossible to trigger this in practice (due to the gas costs
            // involved).
            if (loc + 31) < MAX_U256
                then
                // Write big endian order
                st.Expand(loc,32).Pop().Pop().Write(loc,val).Next()
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Save byte to memory.
     */
    function method MStore8(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var loc := st.Peek(0) as nat;
            var val := (st.Peek(1) % 256) as u8;
            if loc < MAX_U256
                then
                // Write byte
                st.Expand(loc, 1).Pop().Pop().Write8(loc,val).Next()
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
        State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Get word from storage.
    */
    function method SLoad(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 1
        then
            var loc := st.Peek(0);
            var val := st.Load(loc);
            // Push word
            st.Pop().Push(val).KeyAccessed(loc).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
    * Save word to storage.
    */
    function method SStore(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var loc := st.Peek(0);
            var val := st.Peek(1);
            // Store word
            st.Pop().Pop().Store(loc,val).KeyAccessed(loc).Next()
        else
        State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Unconditional branch.
    */
    function method Jump(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 1
        then
            var pc := st.Peek(0);
            // Check valid branch target
            if st.IsJumpDest(pc)
            then
                st.Pop().Goto(pc)
            else
                State.INVALID(INVALID_JUMPDEST)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Unconditional branch.
    */
    function method JumpI(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var pc := st.Peek(0);
            var val := st.Peek(1);
            // Check branch taken or not
            if val == 0 then st.Pop().Pop().Next()
            // Check valid branch target
            else if st.IsJumpDest(pc)
            then
                st.Pop().Pop().Goto(pc)
            else
                State.INVALID(INVALID_JUMPDEST)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
    * Gets value of program counter prior to this instruction being executed.
    */
    function method Pc(st: State) : State
    requires !st.IsFailure()
    {
        //
        if st.Capacity() >= 1 && st.PC() <= MAX_U256
        then
            st.Push(st.PC() as u256).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Get the amount of available gas, including the corresponding reduction
     * for the cost of this instruction.
     */
    function method Gas(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1 && st.Gas() <= (MAX_U256 as nat)
        then
            st.Push(st.Gas() as u256).Next()
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Marks a valid destination for a jump, but otherwise has no effect
     * on machine state.
     */
    function method JumpDest(st: State) : State
    requires !st.IsFailure() {
        st.Next()
    }

    // =====================================================================
    // 60s & 70s: Push Operations
    // =====================================================================

    /**
    * Push one byte onto stack.
    */
    function method Push1(st: State, k: u8) : State
    requires !st.IsFailure() {
        //
        if st.Capacity() >= 1
        then
            st.Push(k as u256).Skip(2)
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Push two bytes onto stack.
     */
    function method Push2(st: State, k: u16) : State
    requires !st.IsFailure() {
        //
        if st.Capacity() >= 1
        then
            st.Push(k as u256).Skip(3)
        else
            State.INVALID(STACK_OVERFLOW)
    }

    /**
     * Push n bytes onto stack.
     */
    function method Push(st: State, bytes: seq<u8>) : State
    requires !st.IsFailure()
    requires |bytes| > 0 && |bytes| <= 32 {
        //
        if st.Capacity() >= 1
        then
            var k := if |bytes| == 1 then (bytes[0] as u256)
            else if |bytes| == 2 then (Bytes.ReadUint16(bytes,0) as u256)
            else if |bytes| <= 4 then (Bytes.ReadUint32(Bytes.LeftPad(bytes,4),0) as u256)
            else if |bytes| <= 8 then (Bytes.ReadUint64(Bytes.LeftPad(bytes,8),0) as u256)
            else if |bytes| <= 16 then (Bytes.ReadUint128(Bytes.LeftPad(bytes,16),0) as u256)
            else
                Bytes.ReadUint256(Bytes.LeftPad(bytes,32),0);
            // Done
            st.Push(k).Skip(|bytes|+1)
        else
            State.INVALID(STACK_OVERFLOW)
    }

    // =====================================================================
    // 80s: Duplication Operations
    // =====================================================================

    /**
    * Duplicate item on stack.
    */
    function method Dup(st: State, k: nat) : State
    requires !st.IsFailure()
    requires k > 0 {
        //
        if st.Operands() > (k-1) && st.Capacity() >= 1
        then
        var kth := st.Peek(k-1);
            st.Push(kth).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 90s: Exchange Operations
    // =====================================================================

    /**
    * Swap two items on the stack
    */
    function method Swap(st: State, k: nat) : State
    requires !st.IsFailure() {
        //
        if st.Operands() > k
        then
            st.Swap(k).Next()
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    // =====================================================================
    // a0s: Logging Operations
    // =====================================================================

    /**
     * Append log with N topics.
     */
    function method LogN(st: State, n:nat) : (nst: State)
    requires !st.IsFailure()
    requires n <= 4 {
        if st.Operands() >= n+2
        then
            var m_loc := st.Peek(0) as nat;
            var len := st.Peek(1) as nat;
            // NOTE: This condition is not specified in the yellow paper.
            // Its not clear whether that was intended or not.  However, its
            // impossible to trigger this in practice (due to the gas costs
            // involved).
            if m_loc + len < MAX_U256
            then
                // Construct log entry.
                var entry := (st.PeekN(n+2)[2..],Memory.Slice(st.evm.memory, m_loc, len));
                // Done
                st.Expand(m_loc,len).Log([entry]).PopN(n+2).Next()
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    // =====================================================================
    // f0s: System operations
    // =====================================================================

    /**
     * Create a new account with associated code.
     */
    function method Create(st: State) : (nst: State)
    requires !st.IsFailure() {
        if st.Operands() >= 3
        then
            var endowment := st.Peek(0);
            // Extract start of initialisation code in memory
            var codeOffset := st.Peek(1) as nat;
            // Extract length of initialisation code
            var codeSize := st.Peek(2) as nat;
            // Copy initialisation code from memory
            var code := Memory.Slice(st.evm.memory, codeOffset, codeSize);
            //
            var nst := st.Expand(codeOffset,codeSize).Pop().Pop().Pop().Next();
            // Pass back continuation
            State.CREATES(nst.evm,endowment,code, None)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Message-call into an account.
     */
    function method Call(st: State) : (nst: State)
    requires !st.IsFailure() {
        //
        if st.Operands() >= 7
        then
            var outSize := st.Peek(6) as nat;
            var outOffset := st.Peek(5) as nat;
            var inSize := st.Peek(4) as nat;
            var inOffset := st.Peek(3) as nat;
            var value := st.Peek(2);
            var to := ((st.Peek(1) as int) % TWO_160) as u160;
            var gas := st.Peek(0) as nat;
            var gascap := GasCalc.CallGasCap(st,gas);
            var callgas := GasCalc.CallGas(st,gas,value);
             // Sanity check bounds
            if (inOffset + inSize) < MAX_U256
            then
                var calldata := Memory.Slice(st.evm.memory, inOffset, inSize);
                // Extract address of this account
                var address := st.evm.context.address;
                // Compute the continuation (i.e. following) state.
                var nst := st.AccountAccessed(address).UseGas(gascap).Expand(inOffset,inSize).Expand(outOffset,outSize).Pop().Pop().Pop().Pop().Pop().Pop().Pop().Next();
                // Pass back continuation.
                State.CALLS(nst.evm, address, to, to, callgas, value, value, calldata, outOffset:=outOffset, outSize:=outSize)
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Message-call into this account with another account's code.
     */
    function method CallCode(st: State) : (nst: State)
    requires !st.IsFailure() {
        //
        if st.Operands() >= 7
        then
            var outSize := st.Peek(6) as nat;
            var outOffset := st.Peek(5) as nat;
            var inSize := st.Peek(4) as nat;
            var inOffset := st.Peek(3) as nat;
            var value := st.Peek(2);
            var to := ((st.Peek(1) as int) % TWO_160) as u160;
            var gas := st.Peek(0) as nat;
            var gascap := GasCalc.CallGasCap(st,gas);
            var callgas := GasCalc.CallGas(st,gas,value);
             // Sanity check bounds
            if (inOffset + inSize) < MAX_U256
            then
                var calldata := Memory.Slice(st.evm.memory, inOffset, inSize);
                // Extract address of this account
                var address := st.evm.context.address;
                // Compute the continuation (i.e. following) state.
                var nst := st.AccountAccessed(address).UseGas(gascap).Expand(inOffset,inSize).Expand(outOffset,outSize).Pop().Pop().Pop().Pop().Pop().Pop().Pop().Next();
                // Pass back continuation.
                State.CALLS(nst.evm, address, address, to, callgas, value, value, calldata, outOffset:=outOffset, outSize:=outSize)
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Halt execution returning output data.
     */
    function method Return(st: State) : State
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
                // Done
                State.RETURNS(gas:=st.evm.gas,data:=data,world:=st.evm.world,substate:=st.evm.substate)
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Message-call into this account with an alternative account's code, but
     * persisting the current values for sender and value.
     */
    function method DelegateCall(st: State) : (nst: State)
    requires !st.IsFailure() {
        //
        if st.Operands() >= 6
        then
            var outSize := st.Peek(5) as nat;
            var outOffset := st.Peek(4) as nat;
            var inSize := st.Peek(3) as nat;
            var inOffset := st.Peek(2) as nat;
            var to := ((st.Peek(1) as int) % TWO_160) as u160;
            var gas := st.Peek(0) as nat;
            var gascap := GasCalc.CallGasCap(st,gas);
            var callgas := GasCalc.CallGas(st,gas,0);
             // Sanity check bounds
            if (inOffset + inSize) < MAX_U256
            then
                var calldata := Memory.Slice(st.evm.memory, inOffset, inSize);
                // Extract call value from enclosing context.
                var callValue := st.evm.context.callValue;
                // Extract sender of this account
                var sender := st.evm.context.sender;
                // Extract address of this account
                var address := st.evm.context.address;
                // Compute the continuation (i.e. following) state.
                var nst := st.AccountAccessed(address).UseGas(gascap).Expand(inOffset,inSize).Expand(outOffset,outSize).Pop().Pop().Pop().Pop().Pop().Pop().Next();
                // Pass back continuation.
                State.CALLS(nst.evm, sender, address, to, callgas, 0, callValue, calldata, outOffset:=outOffset, outSize:=outSize)
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Create a new account with associated code.
     */
    function method Create2(st: State) : (nst: State)
    requires !st.IsFailure() {
        if st.Operands() >= 4
        then
            var endowment := st.Peek(0);
            // Extract start of initialisation code in memory
            var codeOffset := st.Peek(1) as nat;
            // Extract length of initialisation code
            var codeSize := st.Peek(2) as nat;
            // Extract the salt
            var salt := st.Peek(3);
            // Copy initialisation code from memory
            var code := Memory.Slice(st.evm.memory, codeOffset, codeSize);
            //
            var nst := st.Expand(codeOffset,codeSize).Pop().Pop().Pop().Pop().Next();
            // Pass back continuation
            State.CREATES(nst.evm,endowment,code,Some(salt))
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Static Message-call into an account.
     */
    function method StaticCall(st: State) : (nst: State)
    requires !st.IsFailure() {
        //
        if st.Operands() >= 6
        then
            var outSize := st.Peek(5) as nat;
            var outOffset := st.Peek(4) as nat;
            var inSize := st.Peek(3) as nat;
            var inOffset := st.Peek(2) as nat;
            var to := ((st.Peek(1) as int) % TWO_160) as u160;
            var gas := st.Peek(0) as nat;
            var gascap := GasCalc.CallGasCap(st,gas);
            var callgas := GasCalc.CallGas(st,gas,0);
             // Sanity check bounds
            if (inOffset + inSize) < MAX_U256
            then
                var calldata := Memory.Slice(st.evm.memory, inOffset, inSize);
                // Extract address of this account
                var address := st.evm.context.address;
                // Compute the continuation (i.e. following) state.
                var nst := st.AccountAccessed(address).UseGas(gascap).Expand(inOffset,inSize).Expand(outOffset,outSize).Pop().Pop().Pop().Pop().Pop().Pop().Next();
                // Pass back continuation.
                State.CALLS(nst.evm, address, to, to, callgas, 0, 0, calldata, outOffset:=outOffset, outSize:=outSize)
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }
    /**
    * Revert execution returning output data.
    */
    function method Revert(st: State) : State
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
                // Done
                State.REVERTS(gas:=st.evm.gas,data:=data)
            else
                State.INVALID(MEMORY_OVERFLOW)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

    /**
     * Evaluate the STOP bytecode.  This halts the machine without
     * return output data.
     */
    function method SelfDestruct(st: State) : State
    requires !st.IsFailure() {
         //
        if st.Operands() >= 1
        then
            // Determine account to send remaining any remaining funds.
            var acct := (st.Peek(0) as nat) % TWO_160;
            // FIXME: record contract deletion in substate!
            // FIXME: actually refund the account!
            State.RETURNS(gas:=st.Gas(),data:=[],world:=st.evm.world,substate:=st.evm.substate)
        else
            State.INVALID(STACK_UNDERFLOW)
    }

}
