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
    import ByteUtils
    import External
    import GasCalc = Gas
    import opened EvmState
    import opened Optional

    // =====================================================================
    // 0s: Stop and Arithmetic Operations
    // =====================================================================

    /**
     * Evaluate the STOP bytecode.  This halts the machine without
     * return output data.
     */
    function Stop(st: ExecutingState) : State {
        RETURNS(gas:=st.Gas(),data:=[],world:=st.evm.world,substate:=st.evm.substate)
    }

    /**
     * Unsigned integer addition with modulo arithmetic.
     * @param   st  A state.
     * @returns     The state after executing an `ADD` or an `Error` state.
     */
    function Add(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var res := (lhs + rhs) % TWO_256;
            st.Pop(2).Push(res as u256).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Unsigned integer multiplication with modulo arithmetic.
     */
    function Mul(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var res := (lhs * rhs) % TWO_256;
            st.Pop(2).Push(res as u256).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Unsigned integer subtraction with modulo arithmetic.
     */
    function Sub(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var res := (lhs - rhs) % TWO_256;
            st.Pop(2).Push(res as u256).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    // =============================================================================
    // Helpers
    // =============================================================================

    /**
     * Unsigned integer division with handling for zero.
     */
    function DivWithZero(lhs:u256, rhs:u256) : u256 {
        if rhs == 0 then 0 as u256
        else
        (lhs / rhs) as u256
    }

    /**
     * Unsigned integer remainder with handling for zero.
     */
    function ModWithZero(lhs:u256, rhs:u256) : u256 {
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
    function SDivWithZero(lhs:i256, rhs:i256) : i256 {
        if rhs == 0 then 0 as i256
        else if rhs == -1 && lhs == (-TWO_255 as i256)
        then
        -TWO_255 as i256
        else
        // Do not use Dafny's division operator here!
        I256.Div(lhs,rhs)
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
    function SModWithZero(lhs:i256, rhs:i256) : i256 {
        if rhs == 0 then 0 as i256
        else
        // Do not use Dafny's remainder operator here!
        I256.Rem(lhs,rhs)
    }


    /**
     * Unsigned integer division.
     */
    function Div(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1);
            var res := DivWithZero(lhs,rhs) as u256;
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Signed integer division.
     */
    function SDiv(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := Word.asI256(st.Peek(0));
            var rhs := Word.asI256(st.Peek(1));
            var res := Word.fromI256(SDivWithZero(lhs,rhs));
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * (Unsigned) Modulo remainder.
     */
    function Mod(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1);
            var res := ModWithZero(lhs,rhs) as u256;
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Signed integer remainder:
     */
    function SMod(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := Word.asI256(st.Peek(0));
            var rhs := Word.asI256(st.Peek(1));
            var res := Word.fromI256(SModWithZero(lhs,rhs));
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
    * Unsigned integer modulo addition.
    */
    function AddMod(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 3
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    {
        //
        if st.Operands() >= 3
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var rem := st.Peek(2) as int;
            var res := if rem == 0 then 0 else(lhs + rhs) % rem;
            st.Pop(3).Push(res as u256).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     *  Unsigned integer modulo multiplication.
     *
     *  if Peek(2) == 0 then 0 else (Peek(0) * Peek(1)) % Peek(2)
     */
    function MulMod(st: ExecutingState) : (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 3
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    {
        //
        if st.Operands() >= 3
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var rem := st.Peek(2) as int;
            var res := if rem == 0 then 0 else(lhs * rhs) % rem;
            st.Pop(3).Push(res as u256).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Exponential operation
     */
    function Exp(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var base := st.Peek(0) as int;
            var power := st.Peek(1) as int;
            var res := MathUtils.Pow(base,power) % TWO_256;
            st.Pop(2).Push(res as u256).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Extend length of two's complement signed integer.
     */
    function SignExtend(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var width := st.Peek(0);
            var item := st.Peek(1);
            var res := U256.SignExtend(item,width as nat);
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 10s: Comparison & Bitwise Logic Operations
    // =====================================================================

    /**
     * (Unsigned) less-than comparison.
     */
    function Lt(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1);
            if lhs < rhs
                then
                st.Pop(2).Push(1).Next()
            else
                st.Pop(2).Push(0).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
    * (Unsigned) greater-than comparison.
    */
    function Gt(st: ExecutingState) : (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1);
            if lhs > rhs
                then
                st.Pop(2).Push(1).Next()
            else
                st.Pop(2).Push(0).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Signed less-than comparison.
     */
    function SLt(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := Word.asI256(st.Peek(0));
            var rhs := Word.asI256(st.Peek(1));
            if lhs < rhs
                then
                st.Pop(2).Push(1).Next()
            else
                st.Pop(2).Push(0).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Signed greater-than comparison.
     */
    function SGt(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := Word.asI256(st.Peek(0));
            var rhs := Word.asI256(st.Peek(1));
            if lhs > rhs
                then
                st.Pop(2).Push(1).Next()
            else
                st.Pop(2).Push(0).Next()
        else
                ERROR(STACK_UNDERFLOW)
    }

    /**
     * Equality comparison.
     */
    function Eq(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
        var lhs := st.Peek(0);
        var rhs := st.Peek(1);
        if lhs == rhs
            then
            st.Pop(2).Push(1).Next()
        else
            st.Pop(2).Push(0).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Simple not operator.
     */
    function IsZero(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
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
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Bitwise AND operation.
     */
    function And(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as bv256;
            var rhs := st.Peek(1) as bv256;
            var res := (lhs & rhs) as u256;
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Bitwise OR operation.
     */
    function Or(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as bv256;
            var rhs := st.Peek(1) as bv256;
            U256.as_bv256_as_u256(lhs | rhs);
            var res := (lhs | rhs) as u256;
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Bitwise XOR operation.
     */
    function Xor(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as bv256;
            var rhs := st.Peek(1) as bv256;
            U256.as_bv256_as_u256(lhs ^ rhs);
            var res := (lhs ^ rhs) as u256;
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Bitwise NOT operation.
     */
    function Not(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
        //
        if st.Operands() >= 1
        then
            var mhs := st.Peek(0) as bv256;
            var res := (!mhs) as u256;
            st.Pop().Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Retrieve single byte from word.
     */
    function Byte(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var val := st.Peek(1);
            var k := st.Peek(0) as nat;
            var res := if k < 32 then U256.NthUint8(val,k) else 0 as u8;
            st.Pop(2).Push(res as u256).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Left shift operation.
     */
    function Shl(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var rhs := st.Peek(0);
            var lhs := st.Peek(1);
            var res := U256.Shl(lhs,rhs);
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Right shift operation.
     */
    function Shr(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var rhs := st.Peek(0);
            var lhs := st.Peek(1);
            var res := U256.Shr(lhs,rhs);
            st.Pop(2).Push(res).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Arithmetic (signed) right shift operation.
     */
    function Sar(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var rhs := st.Peek(0);
            var lhs := Word.asI256(st.Peek(1));
            var res := I256.Sar(lhs,rhs);
            st.Pop(2).Push(Word.fromI256(res)).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 20s: Keccak256
    // =====================================================================

    /**
     * Computer Keccak256 hash.
     */
    function Keccak256(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 2
        then
            var loc := st.Peek(0) as nat;
            var len := st.Peek(1) as nat;
            var bytes := Memory.Slice(st.evm.memory, loc, len);
            var hash := st.evm.precompiled.Sha3(bytes);
            st.Expand(loc,len).Pop(2).Push(hash).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 30s: Environment Information
    // =====================================================================

    function BlockHash(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
        if st.Operands() >= 1
        then
            // FIXME: what to do here?
            var n := st.Peek(0);
            st.Pop().Push(0).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Get address of currently executing account.
     */
    function Address(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.address as u256).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get balance of the given account.
     */
    function Balance(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
        if st.Operands() >= 1
        then
            // Determine account address
            var account := (st.Peek(0) as nat % TWO_160) as u160;
            // Get balance (or zero if no account exists)
            var balance := if st.evm.world.Exists(account)
                then st.evm.world.Balance(account) else 0;
            // Push balance!
            st.AccountAccessed(account).Pop().Push(balance).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Get execution origination address.  This is the sender of the original
     * transaction; it is never an account with non-empty associated code.
     */
    function Origin(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.origin as u256).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get caller address.
     */
    function Caller(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.sender as u256).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get deposited value by the instruction/transaction responsible for
     * this execution.
     */
    function CallValue(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.callValue).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get input data from the current environment.
     */
    function CallDataLoad(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
        //
        if st.Operands() >= 1
        then
            var loc := st.Peek(0);
            var val := if loc >= st.evm.context.CallDataSize() then 0
                else st.evm.context.CallDataRead(loc);
            st.Pop().Push(val).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Get size of input data in current environment.
     */
    function CallDataSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        //
        if st.Capacity() >= 1
        then
            var len := st.evm.context.CallDataSize();
            st.Push(len).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     *  Copy input data in the current environment to memory.
     */
    function CallDataCopy(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 3
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 3
    {
        //
        if st.Operands() >= 3
        then
            var m_loc := st.Peek(0) as nat;
            var d_loc := st.Peek(1);
            var len := st.Peek(2) as nat;
            // Slice bytes out of call data (with padding as needed)
            var data := st.evm.context.CallDataSlice(d_loc,len as nat);
            // Sanity check
            assert |data| == len;
            // Copy slice into memory
            st.Expand(m_loc as nat, len as nat).Pop(3).Copy(m_loc,data).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Get size of code running in current environment.
     */
    function CodeSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        //
        if st.Capacity() >= 1
        then
            st.Push(Code.Size(st.evm.code)).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Copy code running in current environment to memory.
     */
    function CodeCopy(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 3
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 3
    {
        //
        if st.Operands() >= 3
        then
            var m_loc := st.Peek(0) as nat;
            var d_loc := st.Peek(1) as nat;
            var len := st.Peek(2) as nat;
            var last := (m_loc as nat) + len;
            // Slice bytes out of code (with padding as needed)
            var data := Code.Slice(st.evm.code,d_loc,len);
            // Sanity check
            assert |data| == len;
            // Copy slice into memory
            st.Expand(m_loc as nat, len).Pop(3).Copy(m_loc,data).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Get price of gas in current environment.
     */
    function GasPrice(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.gasPrice).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get size of an account's code.
     */
    function ExtCodeSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
        if st.Operands() >= 1
        then
            // Extract contract account
            var account := (st.Peek(0) as nat % TWO_160) as u160;
            // Sanity check aliveness
            if st.IsDead(account)
            then
                st.AccountAccessed(account).Pop().Push(0).Next()
            else
                // Lookup account
                var data := st.evm.world.GetOrDefault(account);
                // Determine its code size
                var size := |data.code.contents| as u256;
                // Done
                st.AccountAccessed(account).Pop().Push(size).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Copy an account's code to memory.
     */
    function ExtCodeCopy(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 4
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 4
    {
        //
        if st.Operands() >= 4
        then
            // Extract contract account
            var address := (st.Peek(0) as nat % TWO_160) as u160;
            var m_loc := st.Peek(1) as nat;
            var d_loc := st.Peek(2) as nat;
            var len := st.Peek(3) as nat;
            var last := (m_loc as nat) + len;
            // Lookup account data
            var account := st.evm.world.GetOrDefault(address);
            // Slice bytes out of code (with padding as needed)
            var data := Code.Slice(account.code,d_loc,len);
            // Sanity check
            assert |data| == len;
            // Copy slice into memory
            st.AccountAccessed(address).Expand(m_loc as nat, len).Pop(4).Copy(m_loc,data).Next()
         else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Get size of an account's code.
     */
    function ExtCodeHash(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
        if st.Operands() >= 1
        then
            // Extract contract account
            var account := (st.Peek(0) as nat % TWO_160) as u160;
            // Sanity check aliveness
            if st.IsDead(account)
            then
                st.AccountAccessed(account).Pop().Push(0).Next()
            else
                // Lookup account
                var data := st.evm.world.GetAccount(account).Unwrap();
                // Done
                st.AccountAccessed(account).Pop().Push(data.hash).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Get size of return data from the previous call from the current
     * environment.
     */
    function ReturnDataSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            var len := st.evm.context.ReturnDataSize();
            st.Push(len).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     *  Copy return data from previous call to memory.
     */
    function ReturnDataCopy(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(RETURNDATA_OVERFLOW)
    ensures st'.EXECUTING? <==> (st.Operands() >= 3 &&
                         (st.Peek(1) as nat + st.Peek(2) as nat) <= st.evm.context.ReturnDataSize() as nat)
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 3
    {
        //
        if st.Operands() >= 3
        then
            var m_loc := st.Peek(0) as nat;
            var d_loc := st.Peek(1) as nat;
            var len := st.Peek(2) as nat;
            if (d_loc + len) <= (st.evm.context.ReturnDataSize() as nat)
            then
                // Slice bytes out of return data (with padding as needed)
                var data := st.evm.context.ReturnDataSlice(d_loc,len);
                // Sanity check
                assert |data| == len;
                // Copy slice into memory
                st.Expand(m_loc, len).Pop(3).Copy(m_loc,data).Next()
            else
                ERROR(RETURNDATA_OVERFLOW)
        else
            ERROR(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 40s: Block Information
    // =====================================================================

    /**
     * Get the current block's beneficiay address.
     */
    function CoinBase(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.coinBase).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get the current block's timestamp.
     */
    function TimeStamp(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.timeStamp).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get the current block's number.
     */
    function Number(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.number).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get the current block's difficulty.
     */
    function Difficulty(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.difficulty).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get the current block's gaslimit.
     */
    function GasLimit(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.gasLimit).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get the chain ID.
     */
    function ChainID(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.block.chainID).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get balance of currently executing account.
     */
    function SelfBalance(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            // Get address of currently executing account
            var address := st.evm.context.address;
            // Get balance of said account
            var balance := st.evm.world.Balance(address);
            // Done
            st.Push(balance).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Returns the value of the base fee for the currently executing block.
     */
    function BaseFee(st: ExecutingState): (st': State)
    {
        if st.Capacity() >= 1
        then
            // NOTE: needs to be implemented properly!
            st.Push(0).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    // =====================================================================
    // 50s: Stack, Memory Storage and Flow Operations
    // =====================================================================

    /**
     * Pop word from stack.
     */
    function Pop(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 1
        then
            st.Pop().Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Get the size of active memory in bytes.
     */
    function MSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW) || st' == ERROR(MEMORY_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1 && Memory.Size(st.evm.memory) <= MAX_U256
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            var s := Memory.Size(st.evm.memory);
            if s <= MAX_U256
            then
                st.Push(s as u256).Next()
            else
                ERROR(MEMORY_OVERFLOW)
        else
            ERROR(STACK_OVERFLOW)
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
    function MLoad(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
        //
        if st.Operands() >= 1
        then
            var loc := st.Peek(0) as nat;
            // Break out expanded state
            var nst := st.Expand(loc,32);
            // Read from expanded state
            nst.Pop().Push(nst.Read(loc)).Next()
        else
            ERROR(STACK_UNDERFLOW)
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
    function MStore(st: ExecutingState) : (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    {
        //
        if st.Operands() >= 2
        then
            var loc := st.Peek(0) as nat;
            var val := st.Peek(1);
            // Write big endian order
            st.Expand(loc,32).Pop(2).Write(loc,val).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Save byte to memory.
     */
    function MStore8(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    {
        //
        if st.Operands() >= 2
        then
            var loc := st.Peek(0) as nat;
            var val := (st.Peek(1) % 256) as u8;
            // Write byte
            st.Expand(loc, 1).Pop(2).Write8(loc,val).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Get word from storage.
     */
    function SLoad(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
        //
        if st.Operands() >= 1
        then
            var loc := st.Peek(0);
            var val := st.Load(loc);
            // Push word
            st.Pop().Push(val).KeyAccessed(loc).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Save word to storage.
     */
    function SStore(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.EXECUTING? <==> st.Operands() >= 2 && st.WritesPermitted()
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    {
        //
        if st.Operands() >= 2
        then
            if !st.WritesPermitted()
                then ERROR(WRITE_PROTECTION_VIOLATED)
            else
                var loc := st.Peek(0);
                var val := st.Peek(1);
                // Store word
                st.Pop(2).Store(loc,val).KeyAccessed(loc).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Unconditional branch.
     */
    function Jump(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(INVALID_JUMPDEST)
    ensures st'.EXECUTING? <==> st.Operands() >= 1 && st.IsJumpDest(st.Peek(0))
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    {
        //
        if st.Operands() >= 1
        then
            var pc := st.Peek(0);
            // Check valid branch target
            if st.IsJumpDest(pc)
            then
                st.Pop().Goto(pc)
            else
                ERROR(INVALID_JUMPDEST)
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Unconditional branch.
     */
    function JumpI(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(INVALID_JUMPDEST)
    ensures st'.EXECUTING? <==> st.Operands() >= 2 && (st.Peek(1) == 0 || st.IsJumpDest(st.Peek(0)))
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    {
        //
        if st.Operands() >= 2
        then
            var pc := st.Peek(0);
            var val := st.Peek(1);
            // Check branch taken or not
            if val == 0 then st.Pop(2).Next()
            // Check valid branch target
            else if st.IsJumpDest(pc)
            then
                st.Pop(2).Goto(pc)
            else
                ERROR(INVALID_JUMPDEST)
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Gets value of program counter prior to this instruction being executed.
     */
    function Pc(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1 && st.PC() <= MAX_U256
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        //
        if st.Capacity() >= 1 && st.PC() <= MAX_U256
        then
            st.Push(st.PC() as u256).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     * Get the amount of available gas, including the corresponding reduction
     * for the cost of this instruction.
     */
    function Gas(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1 && st.Gas() <= (MAX_U256 as nat)
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1 && st.Gas() <= (MAX_U256 as nat)
        then
            st.Push(st.Gas() as u256).Next()
        else
            ERROR(STACK_OVERFLOW)
    }

    /**
     *  Marks a valid destination for a jump, but otherwise has no effect
     *  on machine state, except incrementing PC.
     *  Equivalent to SKIP instruction semantics-wise.
     */
    function JumpDest(st: ExecutingState): (st': ExecutingState) {
        st.Next()
    }

    /**
     * Perform a static relative jump using a given offset from the position
     * immediately after this instruction.  This instruction does not read any
     * operands from the stack.
     *
     * @note Introduced as part of EIP-4200
     */
    function RJump(st: ExecutingState, offset: i16) : (st':State) {
        // Determine position following this instruction.
        var post_pc := (st.evm.pc + 3) as int;
        // Compute target PC value
        var target := post_pc + (offset as int);
        // Sanity check target address
        if st.IsInstructionBoundary(target)
        then
            st.Goto(target as u256)
        else
            ERROR(INVALID_JUMPDEST)
    }

    /**
     * Perform a conditional static relative jump using a given offset from the
     * position immediately after this instruction.  This pops a value of the
     * stack, and branches based on whether that value is zero or not.  If it is
     * zero, then no branch occurs.  Otherwise, this instruction branches.
     *
     * @note Introduced as part of EIP-4200
     */
    function RJumpI(st: ExecutingState, offset: i16) : (st':State) {
        if st.Operands() >= 1
        then
            var val := st.Peek(0);
            // Check branch taken or not
            if val == 0 then st.Pop(1).Next()
            else
                // Determine position following this instruction.
                var post_pc := (st.evm.pc + 3) as int;
                // Compute target PC value
                var target := post_pc + (offset as int);
                // Sanity check target address
                if st.IsInstructionBoundary(target)
                then
                    st.Pop(1).Goto(target as u256)
                else
                    ERROR(INVALID_JUMPDEST)
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Perform a relative jump via a jump table of one or more relative offsets.
     * This pops a value from the stack and branches to the relative offset
     * given by that index.  If the case value is larger than the number of
     * entries in the jumptable, then execution falls through to the next
     * instruction following this.
     *
     * @note Introduced as part of EIP-4200.
     */
    function RJumpV(st: ExecutingState, table: seq<i16>) : (st':State)
    // More than one but at most 255 entries in the jump table.
    requires 1 <= |table| <= 255 {
        if st.Operands() >= 1
        then
            var val := st.Peek(0) as nat;
            // Check branch taken or not
            if val >= |table| then st.Pop(1).Next()
            else
                // Determine position following this instruction.
                var post_pc := (st.evm.pc + 3) as int;
                // Compute target PC value
                var target := post_pc + (table[val] as int);
                // Sanity check target address
                if st.IsInstructionBoundary(target)
                then
                    st.Pop(1).Goto(target as u256)
                else
                    ERROR(INVALID_JUMPDEST)
        else
            ERROR(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 60s & 70s: Push Operations
    // =====================================================================

    /**
     *  Push zero on the stack.
     *
     *  @param st   A state.
     */
    function Push0(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            st.Push(0).Next()
        else
            ERROR(STACK_OVERFLOW)
    }
    /**
     *  Push bytes on the stack.
     *
     *  @param st   A state.
     *  @param k    The number of bytes to push.
     *
     *  @note       The semantics of the EVM does not seem to require
     *              that k bytes are following the current OPCODE, PUSHk.
     *              So a number of bytes is read and left-padded if not enough
     *              are after PUSHk, and a value is pushed on the stack even
     *              not enough (< k) bytes are available in the code after PUSHk.
     *              As the PC is advanced by k, the next PC will be outside
     *              the code range, and the next opcode to be executed will be defaulted
     *              to 0 (zero) which is the STOP opcode.
     *              In summary: if m < k bytes are following a PUSHk opcode,
     *              a zero-left-padded value of m bytes is pushed on the stack, and
     *              the next instruction is STOP.
     */
    function Push(st: ExecutingState, k: nat): (st': State)
    requires k > 0 && k <= 32
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        if st.Capacity() >= 1
        then
            var bytes := Code.Slice(st.evm.code, (st.evm.pc+1), k);
            assert 0 < |bytes| <= 32;
            var val := ByteUtils.ConvertBytesTo256(bytes);
            st.Push(val).Skip(|bytes|+1)
        else
            ERROR(STACK_OVERFLOW)
    }


    /**
     * Push one byte onto stack.
     */
    function Push1(st: ExecutingState, k: u8) : (st': State) {
        PushN(st,1,k as u256)
    }

    /**
     * Push two bytes onto stack.
     */
    function Push2(st: ExecutingState, k: u16) : (st': State) {
        PushN(st,2,k as u256)
    }

    /**
     * Push three bytes onto stack.
     */
    function Push3(st: ExecutingState, k: u24) : (st': State) {
        PushN(st,3,k as u256)
    }

    /**
     * Push four bytes onto stack.
     */
    function Push4(st: ExecutingState, k: u32) : (st': State) {
        PushN(st,4,k as u256)
    }

    /**
     * Push five bytes onto stack.
     */
    function Push5(st: ExecutingState, k: u40) : (st': State) {
        PushN(st,5,k as u256)
    }

    /**
     * Push six bytes onto stack.
     */
    function Push6(st: ExecutingState, k: u48) : (st': State) {
        PushN(st,6,k as u256)
    }

    /**
     * Push seven bytes onto stack.
     */
    function Push7(st: ExecutingState, k: u56) : (st': State) {
        PushN(st,7,k as u256)
    }

    /**
     * Push eight bytes onto stack.
     */
    function Push8(st: ExecutingState, k: u64) : (st': State) {
        PushN(st,8,k as u256)
    }

    /**
     * Push n bytes from a given word, k, onto the stack.
     */
    function PushN(st: ExecutingState, n:nat, k: u256) : (st': State)
    // Restrict size of constant which can be pushed
    requires 1 <= n <= 32
    // Ensure k is within bounds
    requires (k as nat) <= Int.MaxUnsignedN(n)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1 {
        //
        if st.Capacity() >= 1
        then
            st.Push(k as u256).Skip(n+1)
        else
            ERROR(STACK_OVERFLOW)
    }

    // =====================================================================
    // 80s: Duplication Operations
    // =====================================================================

    /**
    * Duplicate item on stack.
    */
    function Dup(st: ExecutingState, k: nat): (st': State)
    requires k > 0
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1 && st.Operands() >= k
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    {
        //
        if st.Capacity() < 1 then ERROR(STACK_OVERFLOW)
        else if st.Operands() > (k-1)
        then
        var kth := st.Peek(k-1);
            st.Push(kth).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    // =====================================================================
    // 90s: Exchange Operations
    // =====================================================================

    /**
     *  Exchange first (index 0) and k+1-th (index k) item in the stack.
     */
    function Swap(st: ExecutingState, k: nat): (st':State)
    requires 1 <= k <= 16
    ensures st'.EXECUTING? <==> st.Operands() > k
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    {
        if st.Operands() > k
        then
            st.Swap(k).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    // =====================================================================
    // a0s: Logging Operations
    // =====================================================================

    /**
     * Append log with N topics.
     */
    function LogN(st: ExecutingState, n:nat): (st': State)
    requires n <= 4
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.EXECUTING? <==> st.Operands() >= n + 2 && st.WritesPermitted()
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - (n + 2)
    {
        if st.Operands() >= n+2
        then
            if !st.WritesPermitted()
                then
                    ERROR(WRITE_PROTECTION_VIOLATED)
            else
                var m_loc := st.Peek(0) as nat;
                var len := st.Peek(1) as nat;
                // Construct log entry.
                var entry := (st.PeekN(n+2)[2..],Memory.Slice(st.evm.memory, m_loc, len));
                // Done
                st.Expand(m_loc,len).Log([entry]).Pop(n+2).Next()
        else
            ERROR(STACK_UNDERFLOW)
    }

    // =====================================================================
    // f0s: System operations
    // =====================================================================

    /**
     * Create a new account with associated code.
     */
    function Create(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.CONTINUING? <==> (st.Operands() >= 3 && st.WritesPermitted() &&
        st.evm.world.Nonce(st.evm.context.address) < MAX_U64)
    ensures st'.EXECUTING? <==> (st.Operands() >= 3 && st.WritesPermitted() &&
        st.evm.world.Nonce(st.evm.context.address) >= MAX_U64)
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    ensures st' == ERROR(STACK_UNDERFLOW)  <==> st.Operands() < 3
    ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==> st.Operands() >= 3 && !st.WritesPermitted()
    {
        if st.Operands() >= 3
        then
            var endowment := st.Peek(0);
            // Extract start of initialisation code in memory
            var codeOffset := st.Peek(1) as nat;
            // Extract length of initialisation code
            var codeSize := st.Peek(2) as nat;
            // Copy initialisation code from memory
            var code := Memory.Slice(st.evm.memory, codeOffset, codeSize);
            // Calculate available gas
            var gascap := GasCalc.CreateGasCap(st);
            // Apply everything
            var nst := st.Expand(codeOffset,codeSize).Pop(3).Next();
            // Check if the permission for writing has been given
            if !st.WritesPermitted()
            then
                ERROR(WRITE_PROTECTION_VIOLATED)
            else
                // Sanity check nonce
                if st.evm.world.Nonce(st.evm.context.address) < MAX_U64
                then
                    // Charge gas and increment nonce
                    var nnst := nst.UseGas(gascap).IncNonce();
                    // Pass back continuation
                    CONTINUING(CREATES(nnst.evm,gascap,endowment,code,None))
                else
                    // Immediate failure (nonce overflow)
                    nst.Push(0)
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Message-call into an account.
     */
    function Call(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.CONTINUING? <==> st.Operands() >= 7 && (st.WritesPermitted() || st.Peek(2) == 0)
    ensures st' == ERROR(STACK_UNDERFLOW)  <==> st.Operands() < 7
    ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==>
        st.Operands() >= 7 && !st.WritesPermitted() && st.Peek(2) > 0
    {
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
            if !st.WritesPermitted() && value != 0
            then
                ERROR(WRITE_PROTECTION_VIOLATED)
            else
                var calldata := Memory.Slice(st.evm.memory, inOffset, inSize);
                // Extract address of this account
                var address := st.evm.context.address;
                // Compute the continuation (i.e. following) state.
                var nst := st.AccountAccessed(to).UseGas(gascap).Expand(inOffset,inSize).Expand(outOffset,outSize).Pop(7).Next();
                // Pass back continuation.
                CONTINUING(CALLS(nst.evm, address, to, to, callgas, value, value, calldata, st.evm.context.writePermission,outOffset:=outOffset, outSize:=outSize))
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Message-call into this account with another account's code.
     */
    function CallCode(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.CONTINUING? <==> st.Operands() >= 7
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 7
    {
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
            var calldata := Memory.Slice(st.evm.memory, inOffset, inSize);
            // Extract address of this account
            var address := st.evm.context.address;
            // Compute the continuation (i.e. following) state.
            var nst := st.AccountAccessed(to).UseGas(gascap).Expand(inOffset,inSize).Expand(outOffset,outSize).Pop(7).Next();
            // Pass back continuation.
            CONTINUING(CALLS(nst.evm, address, address, to, callgas, value, value, calldata,nst.evm.context.writePermission,outOffset:=outOffset, outSize:=outSize))
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Halt execution returning output data.
     */
    function Return(st: ExecutingState): (st': State)
    ensures st'.RETURNS? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.RETURNS? <==> st.Operands() >= 2
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 2
    {
        //
        if st.Operands() >= 2
        then
            // Determine amount of data to return.
            var len := st.Peek(1) as nat;
            var start := st.Peek(0) as nat;
            // Read out that data.
            var data := Memory.Slice(st.evm.memory, start, len);
            // Done
            RETURNS(gas:=st.evm.gas,data:=data,world:=st.evm.world,substate:=st.evm.substate)
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Message-call into this account with an alternative account's code, but
     * persisting the current values for sender and value.
     */
    function DelegateCall(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.CONTINUING? <==> st.Operands() >= 6
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 6
    {
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
            var calldata := Memory.Slice(st.evm.memory, inOffset, inSize);
            // Extract call value from enclosing context.
            var callValue := st.evm.context.callValue;
            // Extract sender of this account
            var sender := st.evm.context.sender;
            // Extract address of this account
            var address := st.evm.context.address;
            // Compute the continuation (i.e. following) state.
            var nst := st.AccountAccessed(to).UseGas(gascap).Expand(inOffset,inSize).Expand(outOffset,outSize).Pop(6).Next();
            // Pass back continuation.
            CONTINUING(CALLS(nst.evm, sender, address, to, callgas, 0, callValue, calldata, nst.evm.context.writePermission,outOffset:=outOffset, outSize:=outSize))
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Create a new account with associated code.
     */
    function Create2(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.CONTINUING? <==> (st.Operands() >= 4 && st.WritesPermitted() &&
        st.evm.world.Nonce(st.evm.context.address) < MAX_U64)
    ensures st'.EXECUTING? <==> (st.Operands() >= 4 && st.WritesPermitted() &&
        st.evm.world.Nonce(st.evm.context.address) >= MAX_U64)
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 3
    ensures st' == ERROR(STACK_UNDERFLOW)  <==> st.Operands() < 4
    ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==> st.Operands() >= 4 && !st.WritesPermitted()
    {
        if st.Operands() >= 4
            then
                if !st.WritesPermitted()
                    then ERROR(WRITE_PROTECTION_VIOLATED)
                else
                    var endowment := st.Peek(0);
                    // Extract start of initialisation code in memory
                    var codeOffset := st.Peek(1) as nat;
                    // Extract length of initialisation code
                    var codeSize := st.Peek(2) as nat;
                    // Extract the salt
                    var salt := st.Peek(3);
                    // Copy initialisation code from memory
                    var code := Memory.Slice(st.evm.memory, codeOffset, codeSize);
                    // Calculate available gas
                    var gascap := GasCalc.CreateGasCap(st);
                    // Apply everything
                    var nst := st.Expand(codeOffset,codeSize).Pop(4).Next();
                    // Sanity check nonce
                    if st.evm.world.Nonce(st.evm.context.address) < MAX_U64
                       then
                       // Charge gas and increment nonce
                       var nnst := nst.UseGas(gascap).IncNonce();
                       // Pass back continuation
                       CONTINUING(CREATES(nnst.evm,gascap,endowment,code,Some(salt)))
                    else
                        // Immediate failure (nonce overflow)
                        nst.Push(0)
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Static Message-call into an account.
     */
    function StaticCall(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.CONTINUING? <==> st.Operands() >= 6
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 6
    {
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
            var calldata := Memory.Slice(st.evm.memory, inOffset, inSize);
            // Extract address of this account
            var address := st.evm.context.address;
            // Compute the continuation (i.e. following) state.
            var nst := st.AccountAccessed(to).UseGas(gascap).Expand(inOffset,inSize).Expand(outOffset,outSize).Pop(6).Next();
            // Pass back continuation.
            CONTINUING(CALLS(nst.evm, address, to, to, callgas, 0, 0, calldata,false,outOffset:=outOffset, outSize:=outSize))
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Revert execution returning output data.
     */
    function Revert(st: ExecutingState): (st': State)
    ensures st'.IsRevert() || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.IsRevert() <==> st.Operands() >= 2
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 2
    {
        //
        if st.Operands() >= 2
        then
            // Determine amount of data to return.
            var len := st.Peek(1) as nat;
            var start := st.Peek(0) as nat;
            // Read out that data.
            var data := Memory.Slice(st.evm.memory, start, len);
            // Done
            ERROR(REVERTS,gas:=st.evm.gas,data:=data)
        else
            ERROR(STACK_UNDERFLOW)
    }

    /**
     * Evaluate the STOP bytecode.  This halts the machine without
     * return output data.
     */
    function SelfDestruct(st: ExecutingState): (st': State)
    ensures st'.RETURNS? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.RETURNS? <==> st.Operands() >= 1 && st.WritesPermitted()
    ensures st'.RETURNS? ==>
        var a := st.evm.context.address;
        a in st'.world.accounts
        && st'.world.accounts[a] == st.evm.world.accounts[a].(balance := 0)
        && a in st'.substate.selfDestruct
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 1
    ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==> st.Operands() >= 1 && !st.WritesPermitted()
    {
         //
        if st.Operands() >= 1
        then
            if !st.WritesPermitted()
                then
                    ERROR(WRITE_PROTECTION_VIOLATED)
            else
                // Get address of currently executing account
                var address := st.evm.context.address;
                // Get balance of currently executing account
                var balance := st.evm.world.Balance(address);
                // Determine account to send remaining any remaining funds.
                var r := ((st.Peek(0) as nat) % TWO_160) as u160;
                // Register contract deletion in substate!
                var ss := st.evm.substate.AccountAccessed(r).AccountDestructed(address);
                // Apply refund
                var w := if address != r && (!st.Exists(r) || st.evm.world.CanDeposit(r,balance))
                    // Refund balance to r
                    then st.evm.world.EnsureAccount(r).Transfer(address, r, balance)
                    // Otherwise reset balance to zero
                    else st.evm.world.Withdraw(address, balance);
                //
                RETURNS(gas:=st.Gas(),data:=[],world:=w,substate:=ss)
        else
            ERROR(STACK_UNDERFLOW)
    }
}
