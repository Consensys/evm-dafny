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
include "core/memory.dfy"
include "core/precompiled.dfy"
include "core/stack.dfy"
include "core/context.dfy"
include "core/code.dfy"
include "core/fork.dfy"
include "core/storage.dfy"
include "core/substate.dfy"
include "core/transient.dfy"
include "core/worldstate.dfy"
include "util/arrays.dfy"
include "util/extern.dfy"
include "util/int.dfy"
include "opcodes.dfy"

/**
 *  Provide State type to encode the current state of the EVM.
 */
module EvmState {
    import opened Int
    import opened Arrays
    import opened Stack
    import Memory
    import Storage
    import WorldState
    import Context
    import SubState
    import TransientStorage
    import Code
    import opened EvmFork
    import Opcode
    import Precompiled
    import opened Optional

    /**
     * Following included from gas.dfy to avoid circular definition.  However,
     * this is far from ideal.  See #327.
     */
    const G_CODEDEPOSIT: nat := 200

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
    datatype Raw = EVM(
        fork: Fork,
        context: Context.T,
        precompiled: Precompiled.T,
        world : WorldState.T,
        stack   : EvmStack,
        memory  : Memory.T,
        transient : TransientStorage.T,
        code: Code.T,
        substate: SubState.T,
        gas: nat,
        pc : nat
    )

    // An example instantiation of the EVM to satisfy Dafny's witness
    // requirements.  This should not be consider as a valid or useful instance
    // of the EVM though.
    const EVM_WITNESS : Raw := EVM(BERLIN,
            Context.DEFAULT,
            Precompiled.DEFAULT,
            WorldState.Create(map[0:=WorldState.DefaultAccount()]),
            EmptyEvmStack,
            Memory.Create(),
            TransientStorage.Create(),
            Code.Create([]),
            SubState.Create(),
            0,
            0)

    // A valid EVM state must have an entry in the world state for the account
    // being executed.
    type T = c:Raw | c.context.address in c.world.accounts
    // Create simple witness of htis
    witness EVM_WITNESS

    /**
     * The type for executing states.
     */
    type ExecutingState = s:State | s.EXECUTING?
      witness EXECUTING(EVM_WITNESS)

    /**
     * The type for terminated states.
     */
    type TerminatedState = s:State | (s.RETURNS? || s.ERROR?)
    witness ERROR(INSUFFICIENT_GAS)

    /**
     * Identifiers the reason that an exceptional (i.e. INVALID) state was
     * reached. This is not strictly part of the EVM specification (as per the
     * Yellow Paper), but it does provide useful debugging information.
     */
    datatype Error = REVERTS
        | INSUFFICIENT_GAS
        | INSUFFICIENT_FUNDS
        | INVALID_OPCODE
        | STACK_UNDERFLOW
        | STACK_OVERFLOW
        | MEMORY_OVERFLOW
        | BALANCE_OVERFLOW
        | RETURNDATA_OVERFLOW
        | INVALID_JUMPDEST
        | INVALID_PRECONDITION
        | CODESIZE_EXCEEDED
        | CALLDEPTH_EXCEEDED
        | ACCOUNT_COLLISION
        | WRITE_PROTECTION_VIOLATED

    /**
     * Captures the possible state of the machine.  Normal execution is
     * indicated by EXECUTING (with the current machine data).  An exceptional
     * halt is indicated by INVALID (e.g. insufficient gas, insufficient stack
     * operands, etc). Finally, a RETURN or REVERT with return data are
     * indicated accordingly (along with any gas returned).
     */
    datatype State = EXECUTING(evm:T)
        | ERROR(error:Error,gas:nat := 0, data: Array<u8> := [])
        | RETURNS(gas:nat,data: Array<u8>,world: WorldState.T,transient: TransientStorage.T,substate:SubState.T)
        | CONTINUING(Continuation) {

        /**
         * Extract underlying raw state.
         */
        function Unwrap(): T
        requires this.EXECUTING? {
            this.evm
        }

        /**
         * Determine whether this state indicates a user-specified REVERT has
         * occurred or not.
         */
        function IsRevert() : bool {
            this.ERROR? && this.error == REVERTS
        }

        /**
         * Get the fork associated with this EVM state.
         */
        function Fork() : Fork
        requires this.EXECUTING? {
            this.evm.fork
        }

        /**
         * Determine remaining gas.
         */
        function Gas(): nat {
            match this
                case EXECUTING(evm) => evm.gas
                case RETURNS(g, _, _, _, _) => g
                case ERROR(_, g, _) => g
                case CONTINUING(cc) => cc.evm.gas
        }

        /** Use some gas if possible. */
        function UseGas(k: nat): State
        requires this.EXECUTING?
        {
            if this.Gas() < k as nat then
                ERROR(INSUFFICIENT_GAS)
            else
                EXECUTING(evm.(gas := this.Gas() - k as nat))
        }

        /**
         * Refund gas (e.g. after a call)
         */
        function Refund(k: nat): State
        requires this.EXECUTING?
        {
            EXECUTING(evm.(gas := this.Gas() + k as nat))
        }

        /**
         * Determine current PC value.
         */
        function PC(): nat
        requires this.EXECUTING? {
            this.evm.pc
        }

        /**
         * Determine whether a given EIP is active in this EVM.
         */
        predicate IsEipActive(eip: nat) 
        requires this.EXECUTING? {
            this.evm.fork.IsActive(eip)
        }
        
        /**
         * Determine whether modifications to the world state are permitted in this
         * context (true means writes are permitted).
         *  @todo  This should go somewhere else?
         */
        function WritesPermitted(): bool
        requires this.EXECUTING? {
            this.evm.context.writePermission
        }

        // =======================================================================================
        // Memory
        // =======================================================================================

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
        function Expand(address: nat, len: nat): (s': ExecutingState)
        requires this.EXECUTING?
        ensures MemSize() <= s'.MemSize()
        //  If last byte read is in range, no need to expand.
        ensures address + len < MemSize() ==> evm.memory == s'.evm.memory
        {
            if len == 0 then this
            else
                // Determine last address which must be valid after.
                var last := address + len - 1;
                // Expand memory to include at least the last address.
                EXECUTING(evm.(memory:=Memory.Expand(evm.memory, last)))
        }

        /**
         *  Get the size of the memory.
         */
        function MemSize(): nat
        requires this.EXECUTING?
        {
            Memory.Size(evm.memory)
        }

        /**
         * Read word from byte address in memory.
         */
        function Read(address:nat) : u256
        requires this.EXECUTING?
        requires address + 31 < Memory.Size(evm.memory) {
            Memory.ReadUint256(evm.memory,address)
        }

        /**
         * Write word to byte address in memory.
         */
        function Write(address:nat, val: u256) : ExecutingState
        requires this.EXECUTING?
        requires address + 31 < Memory.Size(evm.memory) {
            EXECUTING(evm.(memory:=Memory.WriteUint256(evm.memory,address,val)))
        }

        /**
         * Write byte to byte address in memory.
         */
        function Write8(address:nat, val: u8) : ExecutingState
        requires this.EXECUTING?
        requires address < Memory.Size(evm.memory) {
            EXECUTING(evm.(memory := Memory.WriteUint8(evm.memory,address,val)))
        }

        /**
         * Copy byte sequence to byte address in memory.  Any bytes
         * that overflow are dropped.
         */
        function Copy(address:nat, data: seq<u8>) : ExecutingState
        requires this.EXECUTING?
        requires |data| == 0 || address + |data| <= Memory.Size(evm.memory)
        {
            EXECUTING(evm.(memory:=Memory.Copy(evm.memory,address,data)))
        }

        // =======================================================================================
        // Storage
        // =======================================================================================

        /**
         * Write word to storage
         */
        function Store(address:u256, val: u256) : ExecutingState
        requires this.EXECUTING? {
            var account := evm.context.address;
            EXECUTING(evm.(world:=evm.world.Write(account,address,val)))
        }

        /**
         * Read word from storage
         */
        function Load(address:u256) : u256
        requires this.EXECUTING? {
            var account := evm.context.address;
            evm.world.Read(account,address)
        }

        // =======================================================================================
        // Transient Storage
        // =======================================================================================

        /**
         * Write word to storage
         */
        function TransientStore(address:u256, val: u256) : ExecutingState
        requires this.EXECUTING? {
            var account := evm.context.address;
            EXECUTING(evm.(transient:=evm.transient.Write(account,address,val)))
        }

        /**
         * Read word from storage
         */
        function TransientLoad(address:u256) : u256
        requires this.EXECUTING? {
            var account := evm.context.address;
            evm.transient.Read(account,address)
        }

        /**
         * Determine whether or not an account is considered to be "empty".
         */
        function IsEmpty(account:u160) : bool
        requires this.EXECUTING?
        requires account in evm.world.accounts
        {
            var data := evm.world.accounts[account];
            Code.Size(data.code) == 0 && data.nonce == 0 && data.balance == 0
        }

        /**
         * An account is dead when its account state is non-existent or empty.
         */
        function IsDead(account:u160) : bool
        requires this.EXECUTING?{
            !(account in evm.world.accounts) || IsEmpty(account)
        }

        /**
         * Check whether a given account exists.
         */
        function Exists(account: u160) : bool
        requires this.EXECUTING? {
            // Perform the check
            evm.world.Exists(account)
        }

        /**
         * Increment the nonce associated with the currently executing account.
         */
        function IncNonce() : ExecutingState
        requires this.EXECUTING?
        // The nonce cannot overflow
        requires evm.world.Nonce(evm.context.address) < MAX_U64 {
            EXECUTING(evm.(world:=evm.world.IncNonce(evm.context.address)))
        }

        /**
         * Get the account associated with a given address.  If no such account
         * exists, none is returned.
         */
        function GetAccount(account:u160) : Option<WorldState.Account>
        requires this.EXECUTING? 
        {
            if account in evm.world.accounts
            then
                Some(evm.world.accounts[account])
            else
                None
        }

        /**
         * Create an account at a given address in the world state.  An account
         * cannot already exist at the given address.
         */
        function CreateAccount(address:u160, nonce:nat, balance: u256, storage: map<u256,u256>, code: seq<u8>) : ExecutingState
        requires this.EXECUTING?
        requires !evm.world.Exists(address)
        requires |code| <= Code.MAX_CODE_SIZE {
            // Compute code hash
            var hash := evm.precompiled.Sha3(code);
            // Create account
            var data := WorldState.CreateAccount(nonce,balance,Storage.Create(storage),Code.Create(code),hash);
            // Done
            EXECUTING(evm.(world:=evm.world.Put(address,data)))
        }

        /**
         * Mark a given account as having been "accessed".
         */
        function AccountAccessed(account: u160) : ExecutingState
        requires this.EXECUTING? {
            // Mark address within this account as accessed
            EXECUTING(evm.(substate:=evm.substate.AccountAccessed(account)))
        }

        /**
         * increment/decrement the refund counter of the substate for a given address.
         */
        function ModifyRefundCounter(k: int) : ExecutingState
        requires this.EXECUTING? {
            EXECUTING(evm.(substate:=evm.substate.ModifyRefundCounter(k)))
        }

        /**
         * Check whether a given account was previously accessed (or not).
         */
        function WasAccountAccessed(account: u160) : bool
        requires this.EXECUTING? {
            // Perform the check
            evm.substate.WasAccountAccessed(account)
        }

        /**
         * Mark a given storage location within the currently executing account
         * as having been "accessed" (i.e. read or written).
         */
        function KeyAccessed(address: u256) : ExecutingState
        requires this.EXECUTING? {
            // Determine executing account
            var account := evm.context.address;
            // Mark address within this account as accessed
            EXECUTING(evm.(substate:=evm.substate.KeyAccessed(account,address)))
        }

        /**
         * Check whether a given storage location in the currently executing
         * account was previously accessed or not.
         */
        function WasKeyAccessed(address: u256) : bool
        requires this.EXECUTING? {
            // Determine executing account
            var account := evm.context.address;
            // Perform the check
            evm.substate.WasKeyAccessed(account,address)
        }

        /**
         * Thread through world state and substate from a successful contract
         * call.
         */
        function Merge(world: WorldState.T, transient: TransientStorage.T, substate: SubState.T) : ExecutingState
        requires this.EXECUTING?
        // Contract address for this account must exist.
        requires world.Exists(evm.context.address) {
            EXECUTING(evm.(world:=world,transient:=transient,substate:=substate))
        }

        // =======================================================================================
        // Control Flow
        // =======================================================================================

        /**
         * Decode next opcode from machine.
         */
        function Decode() : u8
        requires this.EXECUTING? { Code.DecodeUint8(evm.code,evm.pc as nat) }

        /**
         * Decode next opcode from machine.
         */
        function OpDecode() : Option<u8>
        {
            if this.EXECUTING?
            then Some(Code.DecodeUint8(evm.code,evm.pc as nat))
            else None
        }

        /**
         * Move program counter to a given location.
         */
        function Goto(k:u256) : ExecutingState
        requires this.EXECUTING? {
            EXECUTING(evm.(pc := k as nat))
        }

        /**
         * Move program counter to next instruction.
         */
        function Next() : ExecutingState
        requires this.EXECUTING? {
            EXECUTING(evm.(pc := evm.pc + 1))
        }

        /**
        * Move program counter over k instructions / operands.
        */
        function Skip(k:nat) : ExecutingState
        requires this.EXECUTING? {
            var pc_k := (evm.pc as nat) + k;
            EXECUTING(evm.(pc := pc_k))
        }

        // =======================================================================================
        // Stack
        // =======================================================================================

        /**
         * Determine number of operands on stack.
         */
        function Operands() : nat
        requires this.EXECUTING? {
            evm.stack.Size()
        }

        /**
         * Get the state of the internal stack.
         */
        function GetStack(): EvmStack
        requires this.EXECUTING? {
            this.evm.stack
        }

        /**
         * Check capacity remaining on stack.
         */
        function Capacity() : nat
        requires this.EXECUTING? {
            evm.stack.Capacity()
        }

        /**
         * Push word onto stack.
         */
        function Push(v: u256) : ExecutingState
        requires this.EXECUTING?
        requires Capacity() > 0 {
            EXECUTING(evm.(stack := GetStack().Push(v)))
        }

        /**
         * peek word from a given position on the stack, where "1" is the
         * topmost position, "2" is the next position and so on.
         */
        function Peek(k: nat): u256
        requires this.EXECUTING?
        // Sanity check peek possible
        requires k < Operands(){
            GetStack().Peek(k)
        }

        /**
         * Peek n words from the top of the stack.  This requires there are
         * enough items on the stack.
         */
        function PeekN(n: nat): (r: seq<u256>)
        requires this.EXECUTING?
        // Sanity check enough items to peek
        requires n <= Operands() {
            GetStack().PeekN(n)
        }

        /**
         *  Extract a slice of the stack.
         *
         *  @param  l   An index.
         *  @param  u   An index.
         *  @returns    A stack made of the first u elements of `st` minus the first `l`.
         */
        function SlicePeek(l: nat, u: nat): (r: EvmStack)
        requires this.EXECUTING?
        requires l <= u <= Operands()
        ensures r.Size() == u - l
        {
            GetStack().Slice(l, u)
        }

        /**
         * Pop n words from stack.
         */
        function Pop(n: nat := 1): ExecutingState
        requires this.EXECUTING?
        // Must pop something
        requires n >= 1
        // Must be enough space!
        requires Operands() >= n {
            EXECUTING(evm.(stack := GetStack().PopN(n)))
        }

        /**
         * Swap top item with kth item.
         */
        function Swap(k: nat): ExecutingState
        requires this.EXECUTING?
        requires Operands() > k > 0 {
            EXECUTING(evm.(stack := GetStack().Swap(k)))
        }

        // =======================================================================================
        // Other
        // =======================================================================================

        /**
         * Append zero or more log entries.
         */
        function Log(entries: seq<SubState.LogEntry>) : ExecutingState
        requires this.EXECUTING? {
            EXECUTING(evm.(substate:=evm.substate.Append(entries)))
        }

        /**
         * Check how many code operands are available.
         */
        function CodeOperands() : int
        requires this.EXECUTING? {
            (Code.Size(evm.code) as nat) - ((evm.pc as nat) + 1)
        }

        /**
         * Update the return data associated with this state.
         */
        function SetReturnData(data: seq<u8>) : ExecutingState
        requires this.EXECUTING?
        requires |data| < TWO_256 {
            EXECUTING(evm.(context:=evm.context.SetReturnData(data)))
        }

        /** The opcode at a given index in the code.
         *
         *  Following the EVM convention, if index is outside the range of code,
         *  returns STOP.
         */
        function CodeAtIndex(index: nat): u8
        requires this.EXECUTING? {
            if index < Code.Size(evm.code) as nat then
                Code.CodeAt(evm.code, index)
            else
                Opcode.STOP
        }

        function CodeAtPC(): u8
        requires this.EXECUTING? { CodeAtIndex(PC()) }

        /**
         * Check whether a given program counter location lies on an instruction
         * boundary.  This is necessary to ensure jumping instructions are
         * valid.  Observe that we permit negative locations here (which are
         * clearly not on an instruction boundary) since that helps when
         * calculating relative offsets.
         */
        predicate IsInstructionBoundary(pc: int)
        requires this.EXECUTING? {
            var len := Code.Size(evm.code) as nat;
            // FIXME: this is not sufficient to establish that the given
            // instruction offset actually lies on an instruction boundary.  See
            // #242.
            pc >= 0 && pc < len
        }

        /**
         * Check whether a given Program Counter location holds the JUMPDEST bytecode.
         */
        predicate IsJumpDest(pc: u256)
        requires this.EXECUTING? {
            this.IsInstructionBoundary(pc as nat) && Code.DecodeUint8(evm.code,pc as nat) == Opcode.JUMPDEST
        }
    }

    /**
     * Begin contract call.
     *
     * @param world The current state of all accounts.
     * @param ctx The context for this call (where e.g. ctx.address is the recipient).
     * @param codeAddress Address of account containing code which should be executed.
     * @param gas The available gas to use for the call.
     * @param depth The current call depth.
     * @param opcode The opcode causing this call.
     */
    function Call(world: WorldState.T, transient: TransientStorage.T, ctx: Context.T, fork: Fork, precompiled: Precompiled.T, substate: SubState.T, codeAddress: u160, value: u256, gas: nat, depth: nat) : State
    // Sender account must exist
    requires world.Exists(ctx.sender)  {
        // Address of called contract
        var address := ctx.address;
        // Check call depth & available balance.  Note there isn't an off-by-one
        // error here (even though it looks like it).
        if depth > 1024 || !world.CanWithdraw(ctx.sender,value) then ERROR(REVERTS, gas)
        else
            // Create default account (if none exists)
            var w := world.EnsureAccount(address);
            // Sanity check deposit won't overflow
            if !w.CanDeposit(address,value) then ERROR(BALANCE_OVERFLOW)
            // Sanity check sufficient funds
            else
                // Transfer wei
                var nw := w.Transfer(ctx.sender,address,value);
                // Check for precompiled contract
                if codeAddress >= 1 && codeAddress <= 9
                then
                    // Call precompiled contract
                    match precompiled.Call(codeAddress,ctx.callData)
                    case None => ERROR(INVALID_PRECONDITION)
                    case Some((data,gascost)) => if gas >= gascost
                        then RETURNS(gas - gascost, data, nw, transient, substate)
                        else ERROR(INSUFFICIENT_GAS)
                // Check for end-user account
                else
                    // Extract contract code
                    var cod := w.GetOrDefault(codeAddress).code;
                    if |cod.contents| == 0 then RETURNS(gas, [], nw, transient, substate)
                    else
                        // Construct fresh EVM
                        var stack := EmptyEvmStack;
                        var mem := Memory.Create();
                        var evm := EVM(fork,ctx,precompiled,nw,stack,mem,transient,cod,substate,gas,0);
                        // Off we go!
                        EXECUTING(evm)
    }

    /**
     * Perform contract creation.
     *
     * @param world The current state of all accounts.
     * @param ctx The context for this call (where e.g. ctx.address is the recipient).
     * @param initcode Initialisation bytecode to execute.
     * @param gas The available gas to use for the call.
     * @param depth The current call depth.
     */
    function Create(world: WorldState.T, transient: TransientStorage.T, ctx: Context.T, fork: Fork, precompiled: Precompiled.T, substate: SubState.T, initcode: seq<u8>, gas: nat, depth: nat) : State
    requires |initcode| <= Code.MAX_CODE_SIZE
    requires world.Exists(ctx.sender) {
        var endowment := ctx.callValue;
        // Check call depth & available balance. Note there isn't an off-by-one
        // error here (even though it looks like it).
        if depth > 1024 || !world.CanWithdraw(ctx.sender,endowment) || !ctx.writePermission then ERROR(REVERTS,gas)
        // Sanity checks for existing account
        else if world.Exists(ctx.address) && !world.CanOverwrite(ctx.address) then ERROR(ACCOUNT_COLLISION)
        else
            var storage := Storage.Create(map[]); // empty
            var account := WorldState.CreateAccount(1,endowment,storage,Code.Create([]),WorldState.HASH_EMPTYCODE);
            // Create initial account
            var w := world.Put(ctx.address,account);
            // Deduct wei
            var nw := w.Withdraw(ctx.sender,endowment);
            // When creating end-use account, return immediately.
            if |initcode| == 0 then RETURNS(gas, [], nw, transient, substate)
            else
                // Construct fresh EVM
                var stack := EmptyEvmStack;
                var mem := Memory.Create();
                var cod := Code.Create(initcode);
                // Mark new account as having been accessed
                var ss := substate.AccountAccessed(ctx.address);
                var evm := EVM(fork,ctx,precompiled,nw,stack,mem,transient,cod,ss,gas,0);
                // Off we go!
                EXECUTING(evm)
    }


    /**
     * Represents an EVM which is currently executing a contract call of some
     * kind (e.g. a `DelegateCall`, `Create`, etc).
     */
    datatype Continuation =
        CALLS(evm: T,
              sender: u160,        // sender
              recipient:u160,      // recipient
              code:u160,           // account whose code to be executed
              gas: nat,            // available gas for call
              callValue: u256,     // value to transfer
              delegateValue: u256, // apparent value in execution context
              callData:seq<u8>,    // input data for call
              writePermission: bool, // Permission to modify state
              outOffset: nat,      // address to write return data
              outSize: nat)        // bytes reserved for return data
        | CREATES(evm:T,
            gas: nat,            // available gas for creation
            endowment: u256,     // endowment
            initcode: seq<u8>,  // initialisation code
            salt: Option<u256>  // optional salt
        ) {

        /**
         * Begin a nested contract call.
         */
        function CallEnter(depth: nat) : State
        requires this.CALLS?
        requires |callData| <= MAX_U256
        // World state must contain this account
        requires evm.world.Exists(sender)
        {
            // Extract what is needed from context
            var origin := evm.context.origin;
            var gasPrice := evm.context.gasPrice;
            var block := evm.context.block;
            var precompiled := evm.precompiled;
            // Construct new context
            var ctx := Context.Create(sender,origin,recipient,delegateValue,callData,writePermission,gasPrice,block);
            // Make the call!
            Call(evm.world,evm.transient,ctx,evm.fork,precompiled,evm.substate,code,callValue,gas,depth+1)
        }

        /**
         * Process a return from a nested call to either an end-user account or
         * a contract.
         */
        function CallReturn(vm:TerminatedState) : (nst:State)
        // Can only return to a continuation (i.e. a parent call)
        requires this.CALLS?
        // Must have enough memory for return data (if any)
        requires outSize == 0 || Memory.Size(evm.memory) >= (outOffset + outSize)
        // Contract address of executing account must still exist.
        requires vm.RETURNS? ==> vm.world.Exists(evm.context.address) {
            // copy over return data, etc.
            var st := EXECUTING(evm);
            if st.Capacity() >= 1
            then
                // Calculate the exitcode
                var exitCode := if vm.RETURNS? then 1 else 0;
                // Extract return data (if applicable)
                if vm.ERROR? && vm.error != REVERTS then st.Push(0).SetReturnData([])
                else
                    // Determine amount of data to actually return
                    var m := Min(|vm.data|,outSize);
                    // Slice out that data
                    var data := vm.data[0..m];
                    // Thread through world state and substate
                    var nst := if vm.RETURNS? then st.Merge(vm.world,vm.transient,vm.substate) else st;
                    // Done
                    nst.Push(exitCode).Refund(vm.gas).SetReturnData(vm.data).Copy(outOffset,data)
            else
                ERROR(STACK_OVERFLOW)
        }


        /**
         * Begin a nested contract creation.
         */
        function CreateEnter(depth: nat, address: u160, initcode: seq<u8>) : State
        requires this.CREATES?
        requires |initcode| <= Code.MAX_CODE_SIZE
        // World state must contain this account
        requires evm.world.Exists(evm.context.address) {
            // Extract what is needed from context
            var sender := evm.context.address;
            var origin := evm.context.origin;
            var gasPrice := evm.context.gasPrice;
            var block := evm.context.block;
            var precompiled := evm.precompiled;
            // Construct new context
            var ctx := Context.Create(sender,origin,address,endowment,[],evm.context.writePermission,gasPrice,block);
            // Make the creation!
            Create(evm.world,evm.transient,ctx,evm.fork,precompiled,evm.substate,initcode,gas,depth+1)
        }

        /**
         * Process a return from a nested contract creation.  This effectively
         * just manages what happens in the parent state. Either the contract
         * address is loaded onto the stack (if successful), or zero is loaded
         * (otherwise).
         */
        function CreateReturn(vm:TerminatedState, address: u160) : (nst:State)
        // Can only return to a continuation (i.e. a parent create)
        requires this.CREATES?
        // Contract address of executing account must still exist.
        requires vm.RETURNS? ==> vm.world.Exists(evm.context.address)
        // Created contract must exist
        requires vm.RETURNS? ==> vm.world.Exists(address) {
            // copy over return data, etc.
            var st := EXECUTING(evm);
            if st.Capacity() >= 1
            then
                if vm.ERROR?
                then
                    var nst := st.AccountAccessed(address).Push(0);
                    // NOTE: only in the event of a REVERT should the return data be passed back.
                    if vm.IsRevert() then nst.Refund(vm.gas).SetReturnData(vm.data)
                    else nst.SetReturnData([])
                else 
                    assert vm.world.Exists(evm.context.address);
                    // Calculate the deposit cost
                    var depositcost := G_CODEDEPOSIT * |vm.data|;
                    // Check code within permitted bounds
                    if |vm.data| > Code.MAX_CODE_SIZE then st.Push(0).SetReturnData([])
                    // Enforce EIP-3541 "Reject new contract code starting with the 0xEF byte"
                    else if this.evm.fork.IsActive(3541) && |vm.data| > 0 && vm.data[0] == Opcode.EOF then st.Push(0).SetReturnData([])
                    // Check sufficient gas for deposit
                    else if vm.gas < depositcost then st.Push(0).SetReturnData([])
                    else
                        // Compute code hash
                        var hash := evm.precompiled.Sha3(vm.data);
                        // Initialise contract code for new account
                        var nworld := vm.world.SetCode(address,vm.data,hash);
                        // Mark account as having been accessed
                        var nvm := vm.substate.AccountAccessed(address);
                        // Thread world state through
                        st.Refund(vm.gas - depositcost).Merge(nworld,vm.transient,nvm).Push(address as u256).SetReturnData([])
            else
                ERROR(STACK_OVERFLOW)
        }
    }
}
