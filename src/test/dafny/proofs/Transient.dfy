include "../../../dafny/evm.dfy"

module Transient {

    import opened Int
    import opened Bytecode
    import opened EVM
    import opened EvmState
    import opened Opcode
    import Stack
    import Gas

    // Some simple tests for transient storage

    method test_1(s1: ExecutingState)
    requires s1.TransientLoad(0) == 0
    {
        var s2 := s1.TransientStore(0,1);
        assert s2.TransientLoad(0) == 1;
    }

    method test_2(s1: ExecutingState)
    requires s1.TransientLoad(0) as nat < MAX_U256
    {
        var k := s1.TransientLoad(0);
        var s2 := s1.TransientStore(0,k+1);
        assert s2.TransientLoad(0) == k+1;
    }

    // The lock contract implements a lock using transient storage.  When the
    // lock is taken, it mutates its storage (by incrementing location 0), and
    // makes an arbitrary call.  Once this is complete, the lock is released.
    // The key property is that a successful call to this contract increments
    // storage[0] at most once.
    const LOCK_CONTRACT : seq<u8> :=
    [
        // If TSTORAGE[0] != 0 then REVERT  
        PUSH0, TLOAD, PUSH2, 0x00, 0x1e , JUMPI,
        // Set TSTORAGE[0]=1
        PUSH1, 0x01, PUSH0, TSTORE,
        // Increment STORAGE[0]
        PUSH0, SLOAD, PUSH1, 0x1, ADD, PUSH0, SSTORE,
        // Call random function
        PUSH0, PUSH0, PUSH0, PUSH0, PUSH0, PUSH0, CALLDATALOAD, GAS, CALL,
        // Set TSTORAGE[0]=0
        PUSH0, PUSH0, TSTORE,
        // Done
        STOP,
        // Revert
        JUMPDEST, PUSH0, PUSH0, REVERT
    ]    

    method block_0_0x0000(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(LOCK_CONTRACT)
    requires st'.WritesPermitted() && st'.PC() == 0x0000 && st'.Gas() <= (MAX_U256 as nat)
    // Stack height(s)
    requires st'.Operands() == 0
    // This evm context cannot change
    ensures st''.EXECUTING? ==> st''.evm.context == st'.evm.context
    // This account must still exist
    ensures st''.RETURNS? ==> st'.evm.context.address in st''.world.accounts.Keys
    // If it terminates normally, then storage[0] incremented by 1
    ensures st''.RETURNS? && (st'.Load(0) as nat) < MAX_U256 ==> st''.world.Read(st'.evm.context.address,0) == st'.Load(0) + 1
    ensures st''.RETURNS? && (st'.Load(0) as nat) == MAX_U256 ==> st''.world.Read(st'.evm.context.address,0) == 0
    // If it terminates normally, then lock was available (i.e. not acquired)
    ensures st''.RETURNS? ==> !LockAcquired(st', st'.evm.context.address)
    // If it terminates normally, then lock is released
    ensures st''.RETURNS? ==> st''.transient.Read(st'.evm.context.address,0) == 0
    {
        var st := st';
        //|fp=0x0000||
        st := Push0(st);
        //|fp=0x0000|0x00|
        st := TLoad(st);
        //|fp=0x0000|_|
        st := Push2(st,0x001e);
        //|fp=0x0000|0x1e,_|
        assume {:axiom} st.IsJumpDest(0x1e);
        st := JumpI(st);
        if st.PC() == 0x1e { st := block_0_0x001e(st); return st;}
        //|fp=0x0000||
        st := Push1(st,0x01);
        //|fp=0x0000|0x01|
        st := Push0(st);
        //|fp=0x0000|0x00,0x01|
        st := TStore(st);
        //|fp=0x0000||
        st := Push0(st);
        st := block_0_0x000b(st);
        return st;
    }

    method block_0_0x000b(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(LOCK_CONTRACT)
    requires st'.WritesPermitted() && st'.PC() == 0x000b && st'.Gas() <= (MAX_U256 as nat)
    // Stack height(s)
    requires st'.Operands() == 1
    // Static stack items
    requires (st'.Peek(0) == 0x0)
    // Lock must be acquired
    requires LockAcquired(st', st'.evm.context.address)
    // This evm context cannot change
    ensures st''.EXECUTING? ==> st''.evm.context == st'.evm.context
    // This account must still exist
    ensures st''.RETURNS? ==> st'.evm.context.address in st''.world.accounts.Keys
    // If it terminates normally, then storage[0] incremented by 1
    ensures st''.RETURNS? && (st'.Load(0) as nat) < MAX_U256 ==> st''.world.Read(st'.evm.context.address,0) == st'.Load(0) + 1
    ensures st''.RETURNS? && (st'.Load(0) as nat) == MAX_U256 ==> st''.world.Read(st'.evm.context.address,0) == 0
    // If it terminates normally, then lock is released
    ensures st''.RETURNS? ==> st''.transient.Read(st'.evm.context.address,0) == 0
    {
        var st := st';
        //|fp=0x0000|0x00|
        st := SLoad(st);
        //|fp=0x0000|_|
        st := Push1(st,0x01);
        //|fp=0x0000|0x01,_|
        st := Add(st);
        //|fp=0x0000|_|
        st := Push0(st);
        //|fp=0x0000|0x00,_|
        st := SStore(st);
        //|fp=0x0000||
        st := Push0(st);
        //|fp=0x0000|0x00|
        st := Push0(st);
        //|fp=0x0000|0x00,0x00|
        st := Push0(st);
        st := block_0_0x0014(st);
        return st;
    }

    method block_0_0x0014(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(LOCK_CONTRACT)
    requires st'.WritesPermitted() && st'.PC() == 0x0014 && st'.Gas() <= (MAX_U256 as nat)
    // Stack height(s)
    requires st'.Operands() == 3
    // Static stack items
    requires (st'.Peek(0) == 0x0 && st'.Peek(1) == 0x0 && st'.Peek(2) == 0x0)
    // Lock must be acquired
    requires LockAcquired(st', st'.evm.context.address)
    // This evm context cannot change
    ensures st''.EXECUTING? ==> st''.evm.context == st'.evm.context
    // This account must still exist
    ensures st''.RETURNS? ==> st'.evm.context.address in st''.world.accounts.Keys
    // No change to storage[0]
    ensures st''.RETURNS? ==> st''.world.Read(st'.evm.context.address,0) == st'.Load(0)
    // If it terminates normally, then lock is released
    ensures st''.RETURNS? ==> st''.transient.Read(st'.evm.context.address,0) == 0
    {
        var st := st';
        //|fp=0x0000|0x00,0x00,0x00|
        st := Push0(st);
        //|fp=0x0000|0x00,0x00,0x00,0x00|
        st := Push0(st);
        //|fp=0x0000|0x00,0x00,0x00,0x00,0x00|
        st := Push0(st);
        //|fp=0x0000|0x00,0x00,0x00,0x00,0x00,0x00|
        st := CallDataLoad(st);
        //|fp=0x0000|_,0x00,0x00,0x00,0x00,0x00|
        st := Bytecode.Gas(st);
        //|fp=0x0000|_,_,0x00,0x00,0x00,0x00,0x00|
        var CONTINUING(cc) := Bytecode.Call(st);
        {
            var inner := cc.CallEnter(1);
            if inner.EXECUTING? { inner := external_call(cc.sender,inner); }
            st := cc.CallReturn(inner);
        }
        //|fp=0x0000|_|
        st := Push0(st);
        //|fp=0x0000|0x00,_|
        st := Push0(st);
        st := block_0_0x001c(st);
        return st;
    }

    method block_0_0x001c(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(LOCK_CONTRACT)
    requires st'.WritesPermitted() && st'.PC() == 0x001c
    // Stack height(s)
    requires st'.Operands() == 3
    // Static stack items
    requires (st'.Peek(0) == 0x0 && st'.Peek(1) == 0x0)
    // This evm context cannot change
    ensures st''.RETURNS?
    // This account must still exist
    ensures st'.evm.context.address in st''.world.accounts.Keys
    // No change to storage[0]
    ensures st''.world.Read(st'.evm.context.address,0) == st'.Load(0)
    // If it terminates normally, then lock is released
    ensures st''.RETURNS? ==> st''.transient.Read(st'.evm.context.address,0) == 0
    {
        var st := st';
        //|fp=0x0000|0x00,0x00,_|
        st := TStore(st);
        //|fp=0x0000|_|
        st := Stop(st);
        return st;
    }

    method block_0_0x001e(st': EvmState.ExecutingState) returns (st'': EvmState.State)
    requires st'.evm.code == Code.Create(LOCK_CONTRACT)
    requires st'.WritesPermitted() && st'.PC() == 0x001e
    // Stack height(s)
    requires st'.Operands() == 0
    // Resulting state always an error
    ensures st''.ERROR?
    {
        var st := st';
        //|fp=0x0000||
        st := JumpDest(st);
        //|fp=0x0000||
        st := Push0(st);
        //|fp=0x0000|0x00|
        st := Push0(st);
        //|fp=0x0000|0x00,0x00|
        st := Revert(st);
        return st;
    }

    method external_call(sender: u160, st: EvmState.ExecutingState) returns (st':EvmState.TerminatedState)
    requires st.Exists(sender)
    // If successful return, account must still exist
    ensures st'.RETURNS? ==> st'.world.Exists(sender) 
    // If the sender's lock was acquired, then its account does not change.
    ensures (st'.RETURNS? && LockAcquired(st,sender)) ==> st.GetAccount(sender) == st'.world.GetAccount(sender) {
        return EvmState.ERROR(EvmState.INSUFFICIENT_GAS); // dummy
    }

    // Helper function to make reading the above easier.
    function LockAcquired(st: EvmState.ExecutingState, account: u160) : bool {
        st.evm.transient.Read(account,0) != 0
    }
}