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
include "util/worldstate.dfy"
include "util/substate.dfy"

module Gas {
	import opened Opcode
	import opened EvmState
    import opened Int
    import opened ExtraTypes
    import opened Memory
    import opened Bytes
    import opened Code
    import opened Context
    import opened WorldState
    import opened SubState

    const G_ZERO: nat := 0;
    const G_JUMPDEST: nat := 1;
	const G_BASE: nat := 2;
	const G_VERYLOW: nat := 3;
	const G_LOW: nat := 5;
	const G_MID: nat := 8;
	const G_HIGH: nat := 10;
    // Cost of a warm account or storage access
    const G_WARMACCESS: nat := 100;
    // Cost of a cold account access.
    const G_COLDACCOUNTACCESS: nat := 2600;
    // Cost of cold storage access
    const G_COLDSLOAD: nat := 2100;
	const G_SSET: nat := 20000;
	const G_SRESET: nat := 2900;
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
	const G_TXDATANONZERO: nat := 16;
	const G_TRANSACTION: nat := 21000;
	const G_LOG: nat := 375;
	const G_LOGDATA: nat := 8;
	const G_LOGTOPIC: nat := 375;
	const G_KECCAK256: nat := 30;
	const G_KECCAK256WORD: nat := 6;
	const G_COPY: nat := 3;
	const G_BLOCKHASH: nat := 20;
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

    /*  Compute the cost of a memory expansion by an arbitrary number of words to cover
     *  a given address and data of length len.
     *
     *  @param   mem         The current memory (also referred to as old memory).
     *  @param   address     The offset to start storing from.
     *  @param   len         The length of data to read or write in bytes.
     *  @results             The number of chunks of 32bytes needed to add to `mem` to cover
     *                       address `address + len - 1`.
     */
    function method ExpansionSize(mem: Memory.T, address: nat, len: nat) : nat
    {
        if len == 0 || address + len - 1 < |mem.contents| then
            0
        else
            // NOTE: there is a bug here as this should not round down.
            var before := |mem.contents| / 32;
            var after := Memory.SmallestLarg32(address + len - 1) / 32;
            QuadraticCostIsMonotonic(after, before);
            assert QuadraticCost(after) >= QuadraticCost(before);
            QuadraticCost(after) - QuadraticCost(before)
    }

    /**
     * Compute the memory expansion cost associated with a given memory address
     * and length, where those values are currently stored on the stack.  If
     * there are insufficient operands on the stack, this returns zero so that a
     * stack underflow can be subsequently reported.
     *
     * @param st Current state
     * @param nOperands Total number of operands expected on the stack.
     * @param locSlot Stack slot containing the location to be accessed.
     * @param length  Number of bytes to read.
     */
    function method CostExpandBytes(st: State, nOperands: nat, locSlot: nat, length: nat) : nat
    requires !st.IsFailure()
    requires nOperands > locSlot {
        if st.Operands() >= nOperands
        then
            var loc := st.Peek(locSlot) as nat;
            ExpansionSize(st.evm.memory,loc,length)
        else
            G_ZERO
    }

    /**
     * Compute the memory expansion cost associated with a given memory range,
     * as determined by an address.  The values of the range, however, are
     * currently stored on the stack and therefore need to be peeked.   If
     * there are insufficient operands on the stack, this returns zero so that a
     * stack underflow can be subsequently reported.
     *
     * @param st Current state
     * @param nOperands Total number of operands expected on the stack.
     * @param locSlot Stack slot containing the location to be accessed.
     * @param lenSlot Stack slot containing the number of bytes to access.
     */
    function method CostExpandRange(st: State, nOperands: nat, locSlot: nat, lenSlot: nat) : nat
    requires !st.IsFailure()
    requires nOperands > locSlot && nOperands > lenSlot {
        if st.Operands() >= nOperands
        then
            var loc := st.Peek(locSlot) as nat;
            var len := st.Peek(lenSlot) as nat;
            ExpansionSize(st.evm.memory,loc,len)
        else
            G_ZERO
    }

    /**
     * Compute the memory expansion cost associated with two memory ranges
     * (a+b), as determined by their respective addresses and lengths.  The
     * values of both ranges, however, are currently stored on the stack and
     * therefore need to be peeked.   If there are insufficient operands on the
     * stack, this returns zero so that a stack underflow can be subsequently
     * reported.
     *
     * @param st Current state
     * @param nOperands Total number of operands expected on the stack.
     * @param aLocSlot Stack slot containing location to be accessed (for first range).
     * @param aLenSlot Stack slot containing the number of bytes to access (for first range).
     * @param bLocSlot Stack slot containing location to be accessed (for second range).
     * @param bLenSlot Stack slot containing the number of bytes to access (for second range).
     */
    function method CostExpandDoubleRange(st: State, nOperands: nat, aLocSlot: nat, aLenSlot: nat, bLocSlot: nat, bLenSlot: nat) : nat
    requires !st.IsFailure()
    requires nOperands > aLocSlot && nOperands > aLenSlot
    requires nOperands > bLocSlot && nOperands > bLenSlot {
        if st.Operands() >= nOperands
        then
            // Determine which range is higher in the address space (hence will
            // determine gas requred).
            var aCost := CostExpandRange(st,nOperands,aLocSlot,aLenSlot);
            var bCost := CostExpandRange(st,nOperands,bLocSlot,bLenSlot);
            Int.Max(aCost,bCost)
        else
            G_ZERO
    }

    /**
     * Compute gas cost for copying bytecodes (e.g. CALLDATACOPY).  The stack
     * slot containing the copy length is provided as an argument as this
     * differs between bytecodes (e.g. EXTCODECOPY vs CODECOPY).
     */
    function method CostCopy(st: State, lenSlot: nat) : nat
        requires !st.IsFailure()
    {
        if st.Operands() > lenSlot
        then
            var len := st.Peek(lenSlot) as nat;
            var n := RoundUp(len,32) / 32;
            (G_COPY * n)
        else
            G_ZERO
    }

    /*
     * Compute gas cost for CREATE2 bytecode.
     * @param st    A non-failure state.
     */
    function method CostCreate2(st: State) : nat
        requires !st.IsFailure()
    {
        if st.Operands() >= 4
        then
            var len := st.Peek(2) as nat;
            var rhs := RoundUp(len,32) / 32;
            G_CREATE + (G_KECCAK256WORD * rhs)
        else
            G_ZERO
    }

    /*
     * Compute gas cost for KECCAK256 bytecode.
     * @param st    A non-failure state.
     */
    function method CostKeccak256(st: State) : nat
        requires !st.IsFailure()
    {
        if st.Operands() >= 2
        then
            var len := st.Peek(1) as nat;
            var rhs := RoundUp(len,32) / 32;
            G_KECCAK256 + (G_KECCAK256WORD * rhs)
        else
            G_ZERO
    }

    /*
     * Compute gas cost for LogX bytecode.
     * @param st    A non-failure state.
     * @param n     The number of topics being logged.
     */
    function method CostLog(st: State, n: nat) : nat
        requires !st.IsFailure()
    {
        if st.Operands() >= 2
        then
            // Determine how many bytes of log data
            var loc := st.Peek(0) as nat;
            var len := st.Peek(1) as nat;
            // Do the calculation!
            G_LOG + (len * G_LOGDATA) + (n * G_LOGTOPIC)
        else
            G_ZERO
    }

    /**
     * Determine the amount of gas for a CALL bytecode only. Note that GasCap is
     * not included here, as this is accounted for separately.
     * @param st A non-failure state
     * @param nOperands number of operands in total required for this bytecode.
     */
    function method CallCost(st: State) : nat
    requires !st.IsFailure() {
        if st.Operands() >= 7
            then
                var value := st.Peek(2) as nat;
                var to := ((st.Peek(1) as int) % TWO_160) as u160;
                CostAccess(st,to) + CostCallXfer(value) + CostCallNew(st,to,value)
        else
            G_ZERO
    }

    /**
     * Determine the amount of gas for a CALLCODE bytecode only. Note
     * that GasCap is not included here, as this is accounted for separately.
     * @param st A non-failure state
     * @param nOperands number of operands in total required for this bytecode.
     */
    function method CallCodeCost(st: State) : nat
    requires !st.IsFailure() {
        if st.Operands() >= 7
            then
                var value := st.Peek(2) as nat;
                var to := ((st.Peek(1) as int) % TWO_160) as u160;
                // NOTE: it is not a mistake that CostCallNew() is left out
                // here.  Despite what the yellow paper says, the new account
                // cost is never charged here.
                CostAccess(st,to) + CostCallXfer(value)
        else
            G_ZERO
    }

    /**
     * Determine the amount of gas for a DELEGATECALL bytecode only. Note that
     * GasCap is not included here, as this is accounted for separately.
     * @param st A non-failure state
     * @param nOperands number of operands in total required for this bytecode.
     */
    function method DelegateCallCost(st: State) : nat
    requires !st.IsFailure() {
        if st.Operands() >= 6
            then
                var to := ((st.Peek(1) as int) % TWO_160) as u160;
                // NOTE: it is not a mistake that CostCallNew() is left out
                // here.  Despite what the yellow paper says, the new account
                // cost is never charged here.
                CostAccess(st,to)
        else
            G_ZERO
    }

    /**
     * Determine the amount of gas for a STATICCALL.
     * @param st A non-failure state
     * @param nOperands number of operands in total required for this bytecode.
     */
    function method StaticCallCost(st: State) : nat
    requires !st.IsFailure() {
        if st.Operands() >= 6
            then
                var to := ((st.Peek(1) as int) % TWO_160) as u160;
                CostAccess(st,to)
        else
            G_ZERO
    }

    /**
     * Determine amount of gas which should be supplied to the caller.
     */
    function method CallGas(st: State, gas: nat, value: u256) : (r:nat)
    requires !st.IsFailure() {
        CallGasCap(st,gas) + CallStipend(value)
    }

    /**
     * Determine whether a stipend should be offered (or not).
     */
    function method CallStipend(value: u256) : (r:nat) {
        if value != 0 then G_CALLSTIPEND else 0
    }

    /**
     * Determine amount of gas which can be supplied to the caller.  Observe
     * that this cannot exceed the amount of available gas!
     */
    function method CallGasCap(st: State, gas: nat) : (r:nat)
    requires !st.IsFailure() {
        Min(L(st.Gas()),gas)
    }

    /**
     * Determine amount of gas which should be provide for a create.
     */
    function method CreateGasCap(st: State) : (r:nat)
    requires !st.IsFailure() {
        L(st.Gas())
    }

    /* YP refers to this function by the name "L" */
    function method L(n: nat): nat { n - (n / 64) }

    /**
     * Determine any additional costs that apply (this is C_extra in the yellow
     * paper)
     */
    function method CostCallExtra(st: State, to: u160, value: nat) : nat
    requires !st.IsFailure() {
        CostAccess(st,to) + CostCallXfer(value) + CostCallNew(st,to,value)
    }

    /**
     * Determine cost for transfering a given amount of value (this is C_xfer in
     * the Yellow paper).
     */
    function method CostCallXfer(value: nat) : nat {
        if value != 0 then G_CALLVALUE else 0
    }

    /**
     * Determine cost for creating an account if applicable (this is C_new in
     * the yellow paper).
     */
    function method CostCallNew(st: State, to: u160, value: nat) : nat
    requires !st.IsFailure() {
        // if the account is DEAD (which is the default account) or does not
        // exists, then charge G_newaccount amount of gas
        if  st.IsDead(to) && (value != 0)
            then G_NEWACCOUNT
        else
            0
    }

    /**
     * Determine cost for accessing a given contract address.
     */
    function method CostExtAccount(st: State) : nat
    requires !st.IsFailure() {
        if st.Operands() >= 1
        then
            // Extract contract account
            var account := (st.Peek(0) as nat % TWO_160) as u160;
            // Cost it!
            CostAccess(st,account)
        else
            G_ZERO
    }

    /**
     * Determine cost for accessing a given contract address (this is C_access
     * in the yellow paper).
     */
    function method CostAccess(st: State, x: u160) : nat
    requires !st.IsFailure() {
        if st.WasAccountAccessed(x) then G_WARMACCESS else G_COLDACCOUNTACCESS
    }

    /**
     * Determine cost for load a given storage location in the currently
     * executing account.
     */
    function method CostSLoad(st: State) : nat
    requires !st.IsFailure()  {
        if st.Operands() >= 1
        then
            var loc := st.Peek(0);
            // Check whether previously accessed or not.
            if st.WasKeyAccessed(loc) then G_WARMACCESS else G_COLDSLOAD
        else
            G_ZERO
    }

    /* this is the "r_dirtyresetclear" function used as part of the gas computation of SSTORE
     * @param   originalVal     it is the value of the storage slot in the pre-transaction state of the account
     * @param   currentVal      it is the  current value of the  storage slot
     * @param   newVal          it is the  new value given as input to the SSTORE opcode as its second argument
     */
    function method DirtyResetClear(originalVal: nat, currentVal: nat, newVal: nat): int
        {
            if originalVal == newVal
                then
                    if originalVal == 0
                        then
                            G_SSET - G_WARMACCESS
                    else
                        G_SRESET - G_WARMACCESS
            else
                0
        }
    /* this is the "r_dirtyclear" function used as part of the gas computation of SSTORE
     * @param   originalVal     it is the value of the storage slot in the pre-transaction state of the account
     * @param   currentVal      it is the  current value of the  storage slot
     * @param   newVal          it is the  new value given as input to the SSTORE opcode as its second argument
     */
    function method DirtyClear(originalVal: nat, currentVal: nat, newVal: nat): int
        {
            if originalVal != 0
                then
                    if currentVal == 0
                        then  0 - R_SCLEAR
                    else if newVal == 0
                        then
                            R_SCLEAR
                    else
                        0
            else
                0
        }

    /* this is part of the  computation of SSTORE gas charge where
       the refund compopnent of the accrued substate ((A_r^)') is computed*/
    function method AccruedSubstateRefund(originalVal: nat, currentVal: nat, newVal: nat): int
        {
            if currentVal != newVal
                then
                    if originalVal == currentVal
                        then
                            if newVal == 0
                                then
                                    R_SCLEAR
                            else
                                0
                    else
                        DirtyClear(originalVal, currentVal, newVal) + DirtyResetClear(originalVal, currentVal, newVal)
            else
                0
        }

    /* computes the part of SSTORE gas cost */
    function method GasCostSSTORE(originalVal: nat, currentVal: nat, newVal: nat): nat
        {
            if currentVal == newVal
                then
                    G_WARMACCESS
            else
                if originalVal == currentVal
                    then
                        if originalVal == 0
                            then
                                G_SSET
                        else
                            G_SRESET
                else
                    G_ZERO
        }

    /* computes both the gas charge and gas refund for SSTORE opcode
     * @param       st      takes a state
     * @returns     a tuple where the first component of the tuple computes the amount of gas to be charged
                    and the second component the amount of wei to be refunded to the originator of the call
     */
    function method CostSSTOREChargeRefund(st: State) : (nat, int)
    requires !st.IsFailure()
        {
            if st.Operands() >= 2 && (st.evm.world.Exists(st.evm.context.address))
            then
                var loc := st.Peek(0);
                var newValue := st.Peek(1);
                var currentAccount := st.evm.world.Get(st.evm.context.address).Unwrap();
                var currentAccountPretransaction := st.evm.world.GetOrDefaultPretransaction(st.evm.context.address);
                // determine if it is a cold or warm storage access and charge accordingly
                var accessCost := if st.WasKeyAccessed(loc) then 0 else G_COLDSLOAD;
                var currentValue := Storage.Read(currentAccount.storage, loc);
                var originalValue := Storage.Read(currentAccountPretransaction.storage, loc);
                // if the current value equals the new value, WARM_STORAGE_READ_COST (which amounts to 100 based on EIP2929) is deducted
                if currentValue == newValue
                    then
                        (G_WARMACCESS + accessCost, 0)
                else
                    if originalValue == currentValue
                        then
                            if newValue == 0
                                then (GasCostSSTORE(originalValue as nat, currentValue as nat, newValue as nat) + accessCost, R_SCLEAR)
                            else
                                (GasCostSSTORE(originalValue as nat, currentValue as nat, newValue as nat) + accessCost, 0)

                    else
                        (G_WARMACCESS + accessCost, AccruedSubstateRefund(originalValue as nat, currentValue as nat, newValue as nat))

            else
                (G_ZERO, G_ZERO)
        }

    // returns the amount of gas to charge upon the execution of SSTORE
    function method CostSSTORE(st: State): nat
    requires !st.IsFailure() {
        if st.Gas() <= G_CALLSTIPEND
        then
            // NOTE: The following forces an out-of-gas exception if the stipend
            // would be jeorpodised, as following the yellow paper.
            MAX_U256
        else
            CostSSTOREChargeRefund(st).0
    }

    // sets in the refund component of the substate the refund amount computed upon the execution of SSTORE
    function method PutRefund(st: State): State
    requires !st.IsFailure() {
        var computeRefund := CostSSTOREChargeRefund(st).1;
        st.ModifyRefundCounter(computeRefund)
        }

    /**
     * Determine cost for deleting a given account.
     */
    function method CostSelfDestruct(st: State) : nat
    requires !st.IsFailure()  {
        if st.Operands() >= 1
        then
            var r := (st.Peek(0) as nat % TWO_160) as u160;
            // Done
            G_SELFDESTRUCT + CostSelfDestructAccess(st,r) + CostSelfDestructNewAccount(st,r)
        else
            G_ZERO
    }

    function method CostSelfDestructAccess(st: State, r: u160) : nat
    requires !st.IsFailure()  {
        if st.WasAccountAccessed(r) then 0 else G_COLDACCOUNTACCESS
    }

    function method CostSelfDestructNewAccount(st: State, r: u160) : nat
    requires !st.IsFailure()  {
        // Extract our address
        var Ia := st.evm.context.address;
        // Check whether refund can happen (or not)
        if st.evm.world.IsDead(r) && st.evm.world.Balance(Ia) != 0 then G_NEWACCOUNT else 0
    }

    function method CostExp(st: State) : nat
    requires !st.IsFailure()  {
        if st.Operands() >= 2
        then
            var exp := st.Peek(1);
            //
            if exp == 0 then G_EXP
            else
                // Compute logarithim
                var l256 := 1 + U256.Log256(exp);
                // Perform gas calc
                G_EXP + (G_EXPBYTE * l256)
        else
            G_ZERO
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
            // 0x50s: Stack, Memory, Storage and Flow
            case POP => s.UseGas(G_BASE)
            case MLOAD => s.UseGas(CostExpandBytes(s,1,0,32) + G_VERYLOW)
            case MSTORE => s.UseGas(CostExpandBytes(s,2,0,32) + G_VERYLOW)
            case MSTORE8 => s.UseGas(CostExpandBytes(s,2,0,1) + G_VERYLOW)
            case SLOAD => s.UseGas(CostSLoad(s))
            case SSTORE => s.UseGas(CostSSTORE(s)) // for now
            case JUMP => s.UseGas(G_MID)
            case JUMPI => s.UseGas(G_HIGH) // for now
            case PC => s.UseGas(G_BASE)
            case MSIZE => s.UseGas(G_BASE)
            case GAS => s.UseGas(G_BASE)
            case JUMPDEST => s.UseGas(G_JUMPDEST)
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
            case CREATE => s.UseGas(CostExpandRange(s,3,1,2) + G_CREATE)
            case CALL => s.UseGas(CostExpandDoubleRange(s,7,3,4,5,6) + CallCost(s))
            case CALLCODE => s.UseGas(CostExpandDoubleRange(s,7,3,4,5,6) + CallCodeCost(s))
            case RETURN => s.UseGas(CostExpandRange(s,2,0,1) + G_ZERO)
            case DELEGATECALL => s.UseGas(CostExpandDoubleRange(s,6,2,3,4,5) + DelegateCallCost(s))
            case CREATE2 => s.UseGas(CostExpandRange(s,4,1,2) + CostCreate2(s))
            case STATICCALL => s.UseGas(CostExpandDoubleRange(s,6,2,3,4,5) + StaticCallCost(s))
            case REVERT => s.UseGas(CostExpandRange(s,2,0,1) + G_ZERO)
            case SELFDESTRUCT => s.UseGas(CostSelfDestruct(s))
            case _ => State.INVALID(INVALID_OPCODE)
    }
}
