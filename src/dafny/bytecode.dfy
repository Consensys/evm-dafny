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

module Bytecode {
    import opened Int
    import U256
    import I256
    import Word
    import Bytes
    import opened EvmState

    // =====================================================================
    // 0s: Stop and Arithmetic Operations
    // =====================================================================

    /**
    * Evaluate the STOP bytecode.  This halts the machine without
    * return output data.
    */
    function method Stop(st: State) : State
    requires !st.IsFailure() {
        var OK(vm) := st;
        //
        State.RETURNS(gas:=vm.gas,data:=[])
    }

    /**
    * Unsigned integer addition with modulo arithmetic.
    */
    function method Add(st: State) : State
    requires !st.IsFailure() {
        var OK(vm) := st;
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0) as int;
            var rhs := st.Peek(1) as int;
            var res := (lhs + rhs) % TWO_256;
            st.Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
                State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            var k := st.Peek(0);
            var res := if k < 32 then U256.NthUint8(val,k as int) else 0;
            st.Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID
    }

    /**
    * Left shift operation.
    */
    function method Shl(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1) as bv256;
            // NOTE: unclear whether shifting is optimal choice here.
            var res := if lhs < 256 then (rhs << lhs) else 0;
            st.Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID
    }

    /**
    * Right shift operation.
    */
    function method {:verify false} Shr(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var lhs := st.Peek(0);
            var rhs := st.Peek(1) as bv256;
            // NOTE: unclear whether shifting is optimal choice here.
            var res := if lhs < 256 then (rhs >> lhs) else 0;
            st.Pop().Pop().Push(res as u256).Next()
        else
            State.INVALID
    }

    // =====================================================================
    // 20s: SHA3
    // =====================================================================

    // =====================================================================
    // 30s: Environment Information
    // =====================================================================

    /**
     * Get address of currently executing account.
     */
    function method Address(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.address as u256).Next()
        else
            State.INVALID
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
            State.INVALID
    }

    /**
     * Get caller address.
     */
    function method Caller(st: State) : State
    requires !st.IsFailure() {
        if st.Capacity() >= 1
        then
            st.Push(st.evm.context.caller as u256).Next()
        else
            State.INVALID
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
            State.INVALID
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
            var val := if loc >= Context.DataSize(st.evm.context) then 0
                else Context.DataRead(st.evm.context,loc);
            st.Pop().Push(val).Next()
        else
            State.INVALID
    }

    /**
     * Get size of input data in current environment.
     */
    function method CallDataSize(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Capacity() >= 1
        then
            var len := |st.evm.context.callData|;
            st.Push(len as u256).Next()
        else
            State.INVALID
    }

    /**
    * Get size of input data in current environment.
    */
    function method CallDataCopy(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 3
        then
            var m_loc := st.Peek(0);
            var d_loc := st.Peek(1);
            var len := st.Peek(2) as int;
            var last := (m_loc as int) + len;
            // NOTE: This condition is not specified in the yellow paper.
            // Its not clear whether that was intended or not.  However, its
            // impossible to trigger this in practice (due to the gas costs
            // involved).
            if last < MAX_U256
            then
                // Slice bytes out of call data (with padding as needed)
                var data := Context.DataSlice(st.evm.context,d_loc,len as u256);
                // Sanity check
                assert |data| == len;
                // Copy slice into memory
                st.Expand(last as u256).Pop().Pop().Pop().Copy(m_loc,data).Next()
            else
                State.INVALID
        else
            State.INVALID
    }

    /**
     * Get size of input data in current environment.
     */
    function method CodeSize(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Capacity() >= 1
        then
            st.Push(Code.Size(st.evm.code)).Next()
        else
            State.INVALID
    }

    /**
     * Get size of input data in current environment.
     */
    function method CodeCopy(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 3
        then
            var m_loc := st.Peek(0);
            var d_loc := st.Peek(1) as nat;
            var len := st.Peek(2) as nat;
            var last := (m_loc as int) + len;
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
                st.Expand(last as u256).Pop().Pop().Pop().Copy(m_loc,data).Next()
            else
                State.INVALID
        else
            State.INVALID
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
            State.INVALID
    }

    // =====================================================================
    // 40s: Block Information
    // =====================================================================


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
            State.INVALID
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
                State.INVALID
        else
            State.INVALID
    }

    /**
     * Get word from memory.
     */
    function method MLoad(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 1
        then
            var loc := st.Peek(0);
            // NOTE: This condition is not specified in the yellow paper.
            // Its not clear whether that was intended or not.  However, its
            // impossible to trigger this in practice (due to the gas costs
            // involved).
            if (loc as int) + 31 <= MAX_U256
                then
                var val := st.Read(loc);
                // Write big endian order
                st.Expand(loc+31).Pop().Push(val).Next()
            else
                State.INVALID
        else
        State.INVALID
    }


    /**
    * Save word to memory.
    */
    function method MStore(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var loc := st.Peek(0);
            var val := st.Peek(1);
            // NOTE: This condition is not specified in the yellow paper.
            // Its not clear whether that was intended or not.  However, its
            // impossible to trigger this in practice (due to the gas costs
            // involved).
            if (loc as int) + 31 <= MAX_U256
                then
                // Write big endian order
                st.Expand(loc+31).Pop().Pop().Write(loc,val).Next()
            else
                State.INVALID
        else
        State.INVALID
    }

    /**
    * Save byte to memory.
    */
    function method MStore8(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            var loc := st.Peek(0);
            var val := (st.Peek(1) % 256) as u8;
            if (loc as int) < MAX_U256
                then
                // Write byte
                st.Expand(loc).Pop().Pop().Write8(loc,val).Next()
            else
                State.INVALID
        else
        State.INVALID
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
            st.Pop().Push(val).Next()
        else
            State.INVALID
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
            st.Pop().Pop().Store(loc,val).Next()
        else
        State.INVALID
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
                State.INVALID
        else
            State.INVALID
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
                State.INVALID
        else
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
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
            State.INVALID
    }

    // =====================================================================
    // a0s: Logging Operations
    // =====================================================================


    // =====================================================================
    // f0s: System operations
    // =====================================================================

    /**
    * Halt execution returning output data.
    */
    function method Return(st: State) : State
    requires !st.IsFailure() {
        //
        if st.Operands() >= 2
        then
            // Determine amount of data to return.
            var len := st.Peek(1) as int;
            var start := st.Peek(0) as int;
            // Sanity check bounds
            if (start+len) <= MAX_U256
            then
                // Read out that data.
                var data := Memory.Slice(st.evm.memory, start as u256, len);
                // Done
                State.RETURNS(gas:=st.evm.gas,data:=data)
            else
                State.INVALID
        else
            State.INVALID
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
            var len := st.Peek(1) as int;
            var start := st.Peek(0) as int;
            // Sanity check bounds
            if (start+len) <= MAX_U256
            then
                // Read out that data.
                var data := Memory.Slice(st.evm.memory, start as u256, len);
                // Done
                State.REVERTS(gas:=st.evm.gas,data:=data)
            else
                State.INVALID
        else
            State.INVALID
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
}
