// The following presents a simulation proof that two sequences of bytecode are
// semantically equivalent.  The two sequences were both generated from the
// following Yul code:
//
// let x := add(sload(0x00),0x01)
// if eq(x,0) { revert(0, 0) }
// sstore(0x00, x)
// stop()
//
// One sequence was generated with optimisation enabled, and the other was not.
include "../../../dafny/evm.dfy"
include "../../../dafny/evms/berlin.dfy"

import opened Int
import opened Opcode
import opened Memory
import opened Bytecode
import opened EvmBerlin
import opened EvmState

// 60016000540160008103601157600080fd5b8060005500
const UNOPT_CODE := [PUSH1,0x01,PUSH1,0x00,SLOAD,ADD,PUSH1,0x00,DUP2,SUB,PUSH1,0x11,JUMPI,PUSH1,0x00,DUP1,REVERT,JUMPDEST,DUP1,PUSH1,0x00,SSTORE,STOP];

// 6001600054018015600f57600055005b600080fd
const OPT_CODE := [PUSH1,0x01,PUSH1,0x00,SLOAD,ADD,DUP1,ISZERO,PUSH1,0x0f,JUMPI,PUSH1,0x00,SSTORE,STOP,JUMPDEST,PUSH1,0x00,DUP1,REVERT];

// This defines a notion of equivalence between two states.  Observe that we
// cannot use full equality because we expect some differences (e.g. the PC
// maybe at a different point, and the code itself will differ, etc).
function equiv(l: State, r: State) : bool {
    if l.EXECUTING? && r.EXECUTING?
    then
        l.evm.memory == r.evm.memory &&
        l.evm.world == r.evm.world &&
        l.evm.context == r.evm.context &&
        l.evm.substate == r.evm.substate
    else if l.RETURNS? && r.RETURNS?
    then
        l.data == r.data && l.world == r.world
    else if l.REVERTS? && r.REVERTS?
    then
        l.data == r.data
    else
        false
}

method proof(context: Context.T, world: map<u160,WorldState.Account>, gas: nat)
requires context.writePermission
requires gas > 100000
requires context.address in world {
    var storage := world[context.address].storage;
    var x := Storage.Read(storage,0) as nat;
    var st1 := EvmBerlin.Create(context,world,gas,UNOPT_CODE);
    var st2 := EvmBerlin.Create(context,world,gas,OPT_CODE);
    //
    st1 := ExecuteN(st1,7); // PUSH1 0x01,PUSH1 0x00,SLOAD,ADD,PUSH1 0x00,DUP2,SUB
    st2 := ExecuteN(st2,6); // PUSH1 0x01,PUSH1 0x00,SLOAD,ADD,DUP1,ISZERO
    assert (st1.Peek(0) as nat) == (x+1) % TWO_256;
    //
    st1 := ExecuteN(st1,2); // PUSH1 0x11, JUMPI
    st2 := ExecuteN(st2,2); // PUSH1 0xf, JUMPI
    //
    if (x+1) == TWO_256 {
        assert st1.PC() == 0xd;
        assert st2.PC() == 0xf;
        st1 := ExecuteN(st1,3);
        st2 := ExecuteN(st2,4);
        assert st1.REVERTS?;
        assert equiv(st1,st2);
    } else {
        assert st1.PC() == 0x11;
        assert st2.PC() == 0xb;
        st1 := ExecuteN(st1,4); // JUMPDEST, DUP1, PUSH1 0x00, SSTORE
        st2 := ExecuteN(st2,2); // PUSH1 0x00, SSTORE
        assert st1.Load(0) == (x+1) as u256;
        assert st2.Load(0) == (x+1) as u256;
        //
        st1 := Execute(st1); // STOP
        st2 := Execute(st2); // STOP
        assert st1.RETURNS? && st2.RETURNS?;
        assert equiv(st1,st2);
    }

}
