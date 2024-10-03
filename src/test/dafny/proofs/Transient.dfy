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
    const LOCK_CONTRACT := Code.Create(
    [
        // If TSTORAGE[0] != 0 then REVERT  
        PUSH0, TLOAD, PUSH1, 0x1d, JUMPI,
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
    )

     /**
     *  Simple proof about the lock contract
     */
    method {:only} lock_proof(st: ExecutingState) returns (st': State)
        /** Initial state with PC = 0 and empty stack. */
        requires st.PC() == 0 && st.Operands() == 0 && st.Fork() == EvmFork.BERLIN
        /** Enough gas. */
        requires st.Gas() >= 40000
        /** Permission to write to storage. */
        requires st.WritesPermitted()
        /** Code is LOCK_CONTRACT. */
        requires st.evm.code == LOCK_CONTRACT
        /** This evm context cannot change */
        ensures st'.EXECUTING? ==> st'.evm.context == st.evm.context
        /** This account must still exist */
        ensures st'.RETURNS? ==> st.evm.context.address in st'.world.accounts.Keys
        /** If it terminates normally, then storage[0] incremented by 1*/
        // ensures st'.RETURNS? && (st.Load(0) as nat) < MAX_U256 ==> st'.world.Read(st.evm.context.address,0) == st.Load(0) + 1
        // ensures st'.RETURNS? && (st.Load(0) as nat) == MAX_U256 ==> st'.world.Read(st.evm.context.address,0) == 0
        /** If it terminates normally, then lock was acquired */
        // ensures st'.RETURNS? ==> st.TransientLoad(0) == 0
        /** If it terminates normally, then lock is released */
        // ensures st'.RETURNS? ==> st'.transient.Read(st.evm.context.address,0) == 0
    {
        st' := st;
        // If TSTORAGE[0] != 0 then REVERT  
        st' := Push0(st');
        st' := TLoad(st');
        var lock := st'.Peek(0);
        st' := Push1(st',0x1d);
        assume {:axiom} st.IsJumpDest(0x1d);
        st' := JumpI(st');        
        if st'.PC() == 0x1d {
            assert lock != 0;
            st' := Push0(st');
            st' := Push0(st');
            st' := Revert(st');
        } else {
            assert lock == 0;
            st' := JumpDest(st');
            // Set TSTORAGE[0]=1
            st' := Push1(st',1);
            st' := Push0(st');
            st' := TStore(st');
            // Increment STORAGE[0]
            st' := Push0(st');
            st' := SLoad(st');
            st' := Push1(st',0x1);
            st' := Add(st');
            st' := Push0(st');
            st' := SStore(st');            
            // Prepare arguments
            st' := Push0(st');
            st' := Push0(st');
            st' := Push0(st');
            st' := Push0(st');
            st' := Push0(st');
            st' := Push0(st');
            st' := CallDataLoad(st');
            st' := Bytecode.Gas(st');
            assert st'.EXECUTING?;
            // >>> Contract call starts here
            var CONTINUING(cc) := Bytecode.Call(st');
            {
                var inner := cc.CallEnter(1);
                inner := randomContract(inner, st'.evm.context.address);
                st' := cc.CallReturn(inner);
            } // <<< Contract call ends here
            // Handle call failure
            if st'.EXECUTING? {
                // Set TSTORAGE[0]=0
                st' := Push0(st');
                st' := Push0(st');
                st' := TStore(st');
                // Success!
                st' := Stop(st');
            }
        } 
    }

    method randomContract(vm:EvmState.ExecutingState, lockAccount: u160) returns (vm':EvmState.State) 
    requires vm.world.Exists(lockAccount)
    ensures vm.world.GetAccount(lockAccount) == vm'.world.GetAccount(lockAccount)
    {
        // This implementation is arbitrary.
        return vm;
    }
}