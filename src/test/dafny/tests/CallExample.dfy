// An set of examples illustrating contract calls.
include "../../../dafny/evm.dfy"
include "../../../dafny/evms/berlin.dfy"
include "../utils.dfy"

module CallExamples {
    import opened Int
    import opened Opcode
    import opened Memory
    import EvmBerlin
    import WorldState
    import opened Bytecode
    import Bytes
    import opened Utils


    /** The gas loaded in the EVM before executing a program. */
    const INITGAS := 0xFFFF

    method {:test} test_call_01() {
        // This is an absolutely minimal example of a contract call where the
        // called contract just stops.  Since the called contract stopped
        // successfully, we can at least check the exit code.
        var vm1 := EvmBerlin.InitEmpty(gas := INITGAS).CreateAccount(0xccc,0,0,map[],[STOP]);
        vm1 := Push1(vm1,0x0); // Out size
        vm1 := Dup(vm1,1);     // Out offset
        vm1 := Dup(vm1,1);     // In size
        vm1 := Dup(vm1,1);     // In offset
        vm1 := Dup(vm1,1);     // Call value
        vm1 := Push2(vm1,0xccc); // To address
        vm1 := Push1(vm1,0x3); // Gas
        // >>> Contract call starts here
        var CONTINUING(cc) := Call(vm1);
        {
            var vm2 := cc.CallEnter(1);
            vm2 := Stop(vm2);
            vm1 := cc.CallReturn(vm2);
        }
        // <<< Contract call ends here
        AssertAndExpect (vm1.EXECUTING?);
        // Check exit code loaded correctly.
        AssertAndExpect (vm1.Peek(0) == 1);
    }

    method {:test} test_call_02() {
        // This is another simple example of a contract call where the called
        // contract raises an exception.
        var vm1 := EvmBerlin.InitEmpty(gas := INITGAS).CreateAccount(0xccc,0,0,map[],[STOP]);
        vm1 := Push1(vm1,0x0); // Out size
        vm1 := Dup(vm1,1);     // Out offset
        vm1 := Dup(vm1,1);     // In size
        vm1 := Dup(vm1,1);     // In offset
        vm1 := Dup(vm1,1);     // Call value
        vm1 := Push2(vm1,0xccc); // To address
        vm1 := Push1(vm1,0x3); // Gas
        // >>> Contract call starts here
        var CONTINUING(cc) := Call(vm1);
        {
            var vm2 := cc.CallEnter(1);
            vm2 := Pop(vm2); // force exception
            vm1 := cc.CallReturn(vm2);
        }
        // <<< Contract call ends here
        AssertAndExpect (vm1.EXECUTING?);
        // Check exit code loaded correctly.
        AssertAndExpect (vm1.Peek(0) == 0);
    }




    method {:test} test_call_03() {
        // This is another simple example of a contract call where the called
        // contract returns some return data.
        var vm1 := EvmBerlin.InitEmpty(gas := INITGAS).CreateAccount(0xccc,0,0,map[],[STOP]);
        vm1 := Push1(vm1,0x20);  // Out size
        vm1 := Push1(vm1,0x0);   // Out offset
        vm1 := Dup(vm1,1);       // In size
        vm1 := Dup(vm1,1);       // In offset
        vm1 := Dup(vm1,1);       // Call value
        vm1 := Push2(vm1,0xccc); // To address
        vm1 := Push1(vm1,0xFF);   // Gas
        // >>> Contract call starts here
        var CONTINUING(cc) := Call(vm1);
        {
            var vm2 := cc.CallEnter(1);
            vm2 := contractReturns123(vm2);
            vm1 := cc.CallReturn(vm2);
        } // <<< Contract call ends here
        // Check exit code loaded correctly.
        AssertAndExpect (vm1.Peek(0) == 1);
        // Extract return data
        vm1 := Push1(vm1,0x00);
        vm1 := MLoad(vm1);
        // Check return data.
        AssertAndExpect (vm1.EXECUTING?);
        AssertAndExpect (vm1.Peek(0) == 0x123);
        AssertAndExpect(vm1.Peek(0) == 0x123);
    }

    method contractReturns123(vm:EvmState.ExecutingState) returns (vm':EvmState.State)
    //can not be a test because it returns a non-failure-compatible type
    requires vm.Capacity() > 3 && vm.MemSize() == 0
    // Returns exactly 32 bytes of data
    ensures vm'.RETURNS? && |vm'.data| == 32
    // World state is unchanged.
    ensures vm.evm.world == vm'.world
    // Returns exactly 0x123
    ensures U256.Read(vm'.data,0) == 0x123 {
        vm' := vm;
        vm' := Push2(vm',0x123);
        vm' := Push1(vm',0x00);
        vm' := MStore(vm');
        vm' := Push1(vm',0x20);
        vm' := Push1(vm',0x00);
        vm' := Return(vm'); // force return
        AssertAndExpect (U256.Read(vm'.data,0) == 0x123);
    }
}
