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
include "util/memory.dfy"
include "util/storage.dfy"
include "util/stack.dfy"
include "util/context.dfy"
include "util/code.dfy"
include "opcodes.dfy"
include "util/ExtraTypes.dfy"

/**
 *  Provide State type to encode the current state of the EVM.
 */
module EvmState {
    import opened Int
    import Stack
    import Memory
    import Storage
    import Context
    import Code
    import Opcode
    import ExtraTypes

    /**
     *  A normal state.
     *
     *  @param  context     An execution context (initiator, etc)
     *  @param  storage     The state of permanent storage
     *  @param  stack       A stack (the EVN is a stack machine)
     *  @param  memory      The state of the memory
     *  @param  code        Some bytecode
     *  @param  gas         The available gas
     *  @param  pc          The program counter pointing to the next
     *                      opcode to be executed.
     *  @note               `pc` is a `nat` and go beyond the range of `code`
     *                      When using this representation you may have to check
     *                      some constrainst on the value of `pc`.
     *  @note               Previous remark applies to `gas`.
     */
    datatype T = EVM(
        context: Context.T,
        storage : Storage.T,
        stack   : Stack.T,
        memory  : Memory.T,
        code: Code.T,
        gas: nat,
        pc : nat
    )

    /** The type for non failure states. */
    type OKState = s:State | !s.IsFailure()
      witness OK(
        EVM(
            Context.Create(0,0,0,0,[],0,Context.Block.Info(0,0,0,0,0,0)),
            Storage.Create(map[]),
            Stack.Create(),
            Memory.Create(),
            Code.Create([]),
            0,
            0
        )
    )

    /**
     * Identifiers the reason that an exceptional (i.e. INVALID) state was
     * reached. This is not strictly part of the EVM specification (as per the
     * Yellow Paper), but it does provide useful debugging information.
     */
    datatype Error = INSUFFICIENT_GAS
        | INVALID_OPCODE
        | STACK_UNDERFLOW
        | STACK_OVERFLOW
        | MEMORY_OVERFLOW
        | INVALID_JUMPDEST
        | CALLDEPTH_EXCEEDED

    /**
     * Captures the possible state of the machine.  Normal execution is
     * indicated by OK (with the current machine data).  An exceptional halt is
     * indicated by INVALID (e.g. insufficient gas, insufficient stack operands,
     * etc). Finally, a RETURN or REVERT with return data are indicated
     * accordingly (along with any gas returned).
     */
    datatype State = OK(evm:T)
        | CALLS(evm:T,
                sender: u160,        // sender
                recipient:u160,      // recipient
                code:u160,           // account whose code to be executed
                gas: nat,            // available gas
                callValue: u256,     // value to transfer
                delegateValue: u256, // apparent value in execution context
                callData:seq<u8>,    // input data for call
                outOffset: nat,      // address to write return data
                outSize: nat)        // bytes reserved for return data
        | INVALID(Error)
        | RETURNS(gas:nat,data:seq<u8>)
        | REVERTS(gas:nat,data:seq<u8>){

        /**
         * Check whether EVM has failed (e.g. due to an exception
         * or a revert, etc) or not.
         */
        predicate method IsFailure() { !this.OK? && !this.CALLS? }

        /**
         * Extract underlying raw state.
         */
        function method Unwrap(): T
        requires !IsFailure() {
            this.evm
        }

        /**
         * Determine number of operands on stack.
         */
        function method Operands() : nat
        requires !IsFailure() {
            Stack.Size(evm.stack)
        }

        /**
         * Determine remaining gas.
         */
        function method Gas(): nat
        requires !this.INVALID? {
            match this
                case OK(evm) => evm.gas
                case CALLS(evm, _, _, _, _, _, _, _, _, _) => evm.gas
                case RETURNS(g, _) => g
                case REVERTS(g, _) => g
        }

        /** Use some gas if possible. */
        function method UseGas(k: nat): State
            requires !IsFailure()
        {
            if this.Gas() < k as nat then
                State.INVALID(INSUFFICIENT_GAS)
            else
                OK(evm.(gas := this.Gas() - k as nat))
        }

        /**
         * Determine current PC value.
         */
        function method PC(): nat
        requires !IsFailure() {
            this.evm.pc
        }

        /**
         * Get the state of the internal stack.
         */
        function method GetStack(): Stack.T
        requires !IsFailure() {
            this.evm.stack
        }

        /**
         *  Expand memory to include a given address.
         *
         *  @param  address The start address.
         *  @param  len     The number of bytes to read from `address`, i.e.
         *                  we want to read `len` bytes starting at `address`.
         *  @returns        A possibly expanded memory that contains
         *                  memory slots upto index `address + len - 1`, unless
         *                  `len==0` in which case it returns the state as is.
         *  @note           This assumes unbounded memory, so the `Memory.Expand`
         *                  call never fails. When using this function, you may check
         *                  first that the extended chunk satisfies some constraints,
         *                  e.g. begin less then `MAX_U256`.
         */
        function method Expand(address: nat, len: nat): (s': State)
            requires !IsFailure()
            ensures !s'.IsFailure()
            ensures MemSize() <= s'.MemSize()
            //  If last byte read is in range, no need to expand.
            ensures address + len < MemSize() ==> evm.memory == s'.evm.memory
        {
            if len == 0 then this
            else
                // Determine last address which must be valid after.
                var last := address + len - 1;
                // Expand memory to include at least the last address.
                OK(evm.(memory:=Memory.Expand(evm.memory, last)))
        }

        /**
         *  Get the size of the memory.
         */
        function method MemSize(): nat
            requires !IsFailure()
        {
            Memory.Size(evm.memory)
        }

        /**
         * Read word from byte address in memory.
         */
        function method Read(address:nat) : u256
        requires !IsFailure()
        requires address + 31 < Memory.Size(evm.memory) {
            Memory.ReadUint256(evm.memory,address)
        }

        /**
         * Write word to byte address in memory.
         */
        function method Write(address:nat, val: u256) : State
        requires !IsFailure()
        requires address + 31 < Memory.Size(evm.memory) {
            OK(evm.(memory:=Memory.WriteUint256(evm.memory,address,val)))
        }

        /**
         * Write byte to byte address in memory.
         */
        function method Write8(address:nat, val: u8) : State
        requires !IsFailure()
        requires address < Memory.Size(evm.memory) {
            OK(evm.(memory := Memory.WriteUint8(evm.memory,address,val)))
        }

        /**
         * Copy byte sequence to byte address in memory.  Any bytes
         * that overflow are dropped.
         */
        function method Copy(address:nat, data: seq<u8>) : State
        requires !IsFailure()
        requires |data| == 0 || address + |data| <= Memory.Size(evm.memory)
        {
            OK(evm.(memory:=Memory.Copy(evm.memory,address,data)))
        }

        /**
         * Write word to storage
         */
        function method Store(address:u256, val: u256) : State
        requires !IsFailure() {
            OK(evm.(storage:=Storage.Write(evm.storage,address,val)))
        }

        /**
         * Read word from storage
         */
        function method Load(address:u256) : u256
        requires !IsFailure() {
            Storage.Read(evm.storage,address)
        }

        /**
         * Decode next opcode from machine.
         */
        function method Decode() : u8
        requires !IsFailure() { Code.DecodeUint8(evm.code,evm.pc as nat) }

        /**
         * Decode next opcode from machine.
         */
        function method OpDecode() : ExtraTypes.Option<u8>
        {
            if this.IsFailure() then ExtraTypes.None
            else ExtraTypes.Some(Code.DecodeUint8(evm.code,evm.pc as nat))
        }

        /**
         * Move program counter to a given location.
         */
        function method Goto(k:u256) : State
        requires !IsFailure() {
            State.OK(evm.(pc := k as nat))
        }

        /**
         * Move program counter to next instruction.
         */
        function method Next() : State
        requires !IsFailure() {
            State.OK(evm.(pc := evm.pc + 1))
        }

        /**
        * Move program counter over k instructions / operands.
        */
        function method Skip(k:nat) : State
        requires !IsFailure() {
            var pc_k := (evm.pc as nat) + k;
            State.OK(evm.(pc := pc_k))
        }

        /**
         * Check capacity remaining on stack.
         */
        function method Capacity() : nat
        requires !IsFailure() {
            Stack.Capacity(evm.stack)
        }

        /**
         * Push word onto stack.
         */
        function method Push(v:u256) : State
        requires !IsFailure()
        requires Capacity() > 0 {
            OK(evm.(stack:=Stack.Push(evm.stack,v)))
        }

        /**
         * peek word from a given position on the stack, where "1" is the
         * topmost position, "2" is the next position and so on.
         */
        function method Peek(k:nat) : u256
        requires !IsFailure()
        // Sanity check peek possible
        requires k < Stack.Size(evm.stack) {
            Stack.Peek(evm.stack,k)
        }

        /**
         * Pop word from stack.
         */
        function method Pop() : State
        requires !IsFailure()
        // Cannot pop from empty stack
        requires Stack.Size(evm.stack) >= 1 {
            OK(evm.(stack:=Stack.Pop(evm.stack)))
        }

        /**
         * Swap top item with kth item.
         */
        function method Swap(k:nat) : State
        requires !IsFailure()
        requires Operands() > k {
            OK(evm.(stack:=Stack.Swap(evm.stack,k)))
        }

        /**
         * Check how many code operands are available.
         */
        function method CodeOperands() : int
        requires !IsFailure() {
            (Code.Size(evm.code) as nat) - ((evm.pc as nat) + 1)
        }

        /**
         * Begin a nested contract call.
         */
        function method CallEnter(storage: map<u256,u256>, code: seq<u8>) : State
        requires this.CALLS?
        requires |callData| <= MAX_U256
        requires |code| <= Code.MAX_CODE_SIZE {
            // Extract what is needed from context
            var sender := evm.context.address;
            var origin := evm.context.origin;
            var gasPrice := evm.context.gasPrice;
            var block := evm.context.block;
            // Construct new context
            var ctx := Context.Create(sender,origin,recipient,callValue,callData,gasPrice,block);
            // Construct fresh EVM
            var stack := Stack.Create();
            var mem := Memory.Create();
            var sto := Storage.Create(storage);
            var cod := Code.Create(code);
            var evm := EVM(evm.context,sto,stack,mem,cod,gas,0);
            // Off we go!
            State.OK(evm)
        }

        /**
         * Process a return from a nested call to either an end-user account or
         * a contract.
         */
        function method CallReturn(vm:State) : (nst:State)
        requires vm.RETURNS? || vm.REVERTS? || vm.INVALID?
        requires this.CALLS?
        requires this.MemSize() >= (outOffset + outSize) {
            // copy over return data, etc.
            var st := OK(evm);
            if st.Capacity() >= 1
            then
                // Calculate the exitcode
                var exitCode := if vm.RETURNS? then 1 else 0;
                // Extract return data (if applicable)
                if vm.INVALID? then st.Push(0)
                else if (outOffset + outSize) <= MAX_U256
                then
                    // Determine amount of data to actually return
                    var m := Min(|vm.data|,outSize);
                    // Slice out that data
                    var data := vm.data[0..m];
                    // NOTE: the follo
                    st.Push(exitCode).Copy(outOffset,data)
                else
                    INVALID(MEMORY_OVERFLOW)
            else
                INVALID(STACK_UNDERFLOW)
        }

        /**
         * Check whether a given Program Counter location holds the JUMPDEST bytecode.
         */
        predicate method IsJumpDest(pc: u256)
        requires !IsFailure() {
            pc < Code.Size(evm.code) && Code.DecodeUint8(evm.code,pc as nat) == Opcode.JUMPDEST
        }
    }
}
