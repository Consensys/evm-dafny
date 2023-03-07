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

include "../../../dafny/evms/berlin.dfy"

/**
 *  Provide some simple simulation checks.
 */
module SimulationChecks {

    import opened Int
    import opened EvmBerlin
    import opened Bytecode
    import opened EvmState
    import opened Opcode

    /**
     *  Compare two VMs states. Equality is wrt to all state components except code and PC.
     *  @note   Gas can be ignored too if needed.
     */
    predicate equiv(l: State, r: State) {
        if l.EXECUTING? && r.EXECUTING?
        then
            l.evm.memory == r.evm.memory &&
            l.evm.world == r.evm.world &&
            l.evm.context == r.evm.context &&
            l.evm.substate == r.evm.substate &&
            l.evm.gas == r.evm.gas
        else if l.RETURNS? && r.RETURNS?
        then
            l.data == r.data && l.world == r.world
        else if l.ERROR? && r.ERROR?
        then
            l.data == r.data
        else
            false
    }

    /** Use the functional definition of the EVM to check refinement.
     *  this is a very simple program just to check we can start two machines
     *  and Execute one step.
     */
    method main0Func(g: nat)
        requires g  >= Gas.G_VERYLOW
    {
        // Initialise EVM #1
        var vm1 := EvmBerlin.InitEmpty(g, [PUSH1, 1, PUSH1, 0x2, ADD, POP, STOP]);

        //  EVM #2, no code associated with.
        //  to be able to satisfy the pre-condition of Push1 etc we still need
        //  some bytecode of the same size to be able to advance `pc` (this check is part of
        //  Push1 and others)
        var vm2 := EvmBerlin.InitEmpty(g);

        //  First check: initial states are equiv.
        assert equiv(vm1, vm2);

        //  Execute one instruciton in each machine and check equiv.
        vm2 := Bytecode.Push1(vm2.UseGas(Gas.G_VERYLOW), 1);
        vm1 := EvmBerlin.Execute(vm1);
        assert equiv(vm1, vm2);
    }

    /**
     *  A very simple program manipulating the stack.
     *  There is no loop in this program and not branching.
     *
     *  If this program is correct, then the program P1 in main1,
     *  simulates the program P2 (in e2).
     *
     *  The simulation is encoded as a two-player game:
     *  0. the two programs P1 and P2 start in initial state of machines e1 and e2
     *  1. e2 makes a move
     *  2. e1 chooses a move to match (simulate) it (or nothing, see STOP at the
     *      end of main1).
     *  We define the simulation relation to be `equiv`.
     *  P1 simulates P2 if, starting in states (s1, s2) with equiv(s1, s2), if
     *  P2 makes a move s2 - i2 -> s2' (executes an instruction i), then P1 can
     *  make a move s1 - i1 -> s1' and equiv(s1', s2').
     *
     *  To check the previous property we assert `equiv` after each move.
     *
     */
    method main1(g: nat)
        requires g >= 3 * Gas.G_VERYLOW + Gas.G_BASE + Gas.G_ZERO //  gas is not used in the functional evm implementation.
    {
        var a: u8 := 0x01;
        var b : u8 := 0x02;

        //  EVM #1
        // Initialise EVM #1
        var vm1 := EvmBerlin.InitEmpty(g, [PUSH1, a, PUSH1, b, ADD, POP, STOP]);

        //  EVM #2, no code associated with.
        //  to be able to satisfy the pre-condition of Push1 etc we still need
        //  some bytecode of the same size to be able to advance `pc` (this check is part of
        //  Push1 and others)
        var vm2 := EvmBerlin.InitEmpty(g);

        //  First check.
        assert equiv(vm1, vm2);

        //  Now run some instructions and check equiv after each of them.
        vm2 := Bytecode.Push1(vm2.UseGas(Gas.G_VERYLOW), a);
        vm1 := EvmBerlin.Execute(vm1);
        assert equiv(vm1, vm2);

        vm2 := Bytecode.Push1(vm2.UseGas(Gas.G_VERYLOW), b);
        vm1 := EvmBerlin.Execute(vm1);
        assert equiv(vm1, vm2);

        vm2 := Bytecode.Add(vm2.UseGas(Gas.G_VERYLOW));
        vm1 := EvmBerlin.Execute(vm1);
        assert equiv(vm1, vm2);

        assert vm2.Peek(0) == a as u256 + b as u256;
        assert vm1.Peek(0) == a as u256 + b as u256;

        vm2 := Bytecode.Pop(vm2.UseGas(Gas.G_BASE));
        vm1 := EvmBerlin.Execute(vm1);
        assert equiv(vm1, vm2);

        assert vm2.evm.stack == vm1.evm.stack;

        vm2 := Bytecode.Stop(vm2.UseGas(Gas.G_ZERO));
        vm1 := EvmBerlin.Execute(vm1);
        assert equiv(vm1, vm2);
    }

    /**
     *  In this next example, we use a variation of the previous game.
     *  The objective is to prove that the program in main5 simulates
     *  the bytecode running in e.
     *
     *  To do so, we still play a game between main5 (P1) and the bytecode (P2) but
     *  we can encode it in a single instruction.
     *  To do we use a special mode of e: track bytecode (`checkCode` is set).
     *  The execution of an instruction like e.push(c) in main5 is interpreted as follows:
     *      1. P2 executes the instruction at pc (and pc is modified)
     *      2. P1 matches it by a push(c)
     *      3. the `checkCode` features in e checks that the current
     *          instruction at pc is indeed a push(c)
     *  If P1 can always guess the right instruction,
     *  then main5 simulates the bytecode!
     *  Overall, this reduces to checking that main5 is correct.
     *
     *  @param  c   The number of times to iterate the loop.
     *  @param  g   The initial amount of gas.
     */
    method main5(c: u8, g: nat)
        requires g >= 0 // Gas ignored in this example
    {
        var end : u8 := 17;
        var a: u8 := 0x01;
        var b : u8 := 0x02;

        //  EVM
        // Initialise EVM
        var vm := EvmBerlin.InitEmpty(g,
            [
                PUSH1, c,       //  0
                JUMPDEST,       //  2
                DUP1,           //  3
                ISZERO,         //  4
                DUP1,           //  5
                PUSH1, end,     //  6
                JUMPI,          //  8
                POP,            //  9
                PUSH1, 1,       // 10
                SWAP1,          // 12
                SUB,            // 13
                PUSH1, 2,       // 14
                JUMP,           // 16
                JUMPDEST,       // 17
                STOP            // 18
            ]
        );

        //  Snapshot of code. As it is a variable it may be modified
        //  byt the program and we want to show that it is constant.
        ghost var code_ := vm.evm.code;

        ghost var count :u256 := c as u256;

        //  Push input on the stack
        //  Check that pc is zero and code under pc is push1
        assert vm.PC() == 0;
        assert vm.CodeAtPC() == PUSH1;
        assert vm.CodeAtIndex(vm.PC() + 1) == c;
        assert vm.GetStack() == Stack.Empty;

        vm := Bytecode.Push1(vm, c);
        assert vm.GetStack() == Stack.Make([count]);
        assert vm.Peek(0) == count;

        vm := Bytecode.JumpDest(vm);
        assert vm.GetStack() == Stack.Make([count]);
        assert vm.Peek(0) == count;

        // Compute result of test c > 0
        assert vm.CodeAtPC() == DUP1;
        vm := Bytecode.Dup(vm, 1);
        assert vm.GetStack() == Stack.Make([count, count]);

        assert vm.CodeAtPC() == ISZERO;
        vm := Bytecode.IsZero(vm);
        assert vm.GetStack() == Stack.Make([if count == 0 then 1 else 0, count]);

        assert vm.CodeAtPC() == DUP1;
        vm := Bytecode.Dup(vm, 1);
        assert vm.GetStack() == Stack.Make([if count == 0 then 1 else 0, if count == 0 then 1 else 0, count]);

        //  If count == 0 jump to end
        assert vm.CodeAtPC() == PUSH1;
        assert vm.evm.code.contents[vm.evm.pc + 1] == end;
        vm := Bytecode.Push1(vm, end);
        assert vm.GetStack() == Stack.Make([end as u256, if count == 0 then 1 else 0, if count == 0 then 1 else 0, count]);

        assert vm.CodeAtPC() == JUMPI;
        vm := Bytecode.JumpI(vm);
        assert vm.GetStack() == Stack.Make([if count == 0 then 1 else 0, count]);

        //  Check the top of the stack to predict whether the body is executed or not.
        while vm.Peek(0) == 0 //
            invariant vm.EXECUTING?
            invariant vm.evm.code.contents == code_.contents   //  code is not changed
            invariant |vm.evm.stack.contents| > 1              //  stack not empty
            invariant vm.Capacity() >= 2                       //  capacity >= 2 on entry
            invariant vm.Peek(1) == count                      //  second element is = count
            invariant count == 0 <==> vm.Peek(0) > 0
            invariant vm.Peek(0) == 0 <==> vm.PC() == 9
            invariant vm.Peek(0) > 0 <==> vm.PC() == 17
            invariant vm.Gas() >= 0 //  Gas ignored.

            decreases count
        {
            assert vm.evm.stack.contents[..2] == [0, count];

            assert vm.CodeAtPC() == POP;
            vm := Bytecode.Pop(vm);
            assert vm.evm.stack.contents[..1] == [count];

            assert vm.CodeAtPC() == PUSH1;
            assert vm.CodeAtIndex(vm.PC() + 1) == 0x1;
            vm := Bytecode.Push1(vm, 1);
            assert vm.SlicePeek(0, 2) == Stack.Make([1, count]);

            assert vm.CodeAtPC() == SWAP1;
            vm := Bytecode.Swap(vm, 1);
            assert vm.SlicePeek(0, 2) == Stack.Make([count,1 ]);

            assert vm.CodeAtPC() == SUB;
            vm := Bytecode.Sub(vm);
            assert vm.SlicePeek(0, 1) == Stack.Make([count - 1]);

            assert vm.CodeAtPC() == PUSH1;
            assert vm.CodeAtIndex(vm.PC() + 1) == 0x2;
            vm := Bytecode.Push1(vm, 2);
            assert vm.Peek(1) == count - 1;
            assert vm.SlicePeek(0, 2) == Stack.Make([2, count - 1]);

            assert vm.CodeAtPC() == JUMP;
            vm := Bytecode.Jump(vm);
            assert vm.SlicePeek(0, 1) == Stack.Make([count - 1]);

            assert vm.CodeAtPC() == JUMPDEST;
            vm := Bytecode.JumpDest(vm);
            assert vm.SlicePeek(0, 1) == Stack.Make([count - 1]);

            // Compute result of test c > 0, same as before the loop
            count := count - 1;

            assert vm.CodeAtPC() == DUP1;
            vm := Bytecode.Dup(vm, 1);
            assert vm.Peek(0) == count;
            assert vm.Peek(1) == count;
            assert vm.SlicePeek(0, 2) == Stack.Make([count, count]);

            assert vm.CodeAtPC() == ISZERO;
            vm := Bytecode.IsZero(vm);
            assert vm.SlicePeek(0, 2) == Stack.Make([if count == 0 then 1 else 0, count]);

            assert vm.CodeAtPC() == DUP1;

            vm := Bytecode.Dup(vm, 1);
            assert vm.EXECUTING?;
            assert vm.SlicePeek(0, 3) == Stack.Make([if count == 0 then 1 else 0, if count == 0 then 1 else 0, count]);

            //  if count == 0 jump to end
            assert vm.CodeAtPC() == PUSH1;
            assert vm.CodeAtIndex(vm.PC() + 1) == end;
            vm := Bytecode.Push1(vm, end);
            assert vm.GetStack().contents[1] == if count == 0 then 1 else 0;
            assert vm.Peek(0) == end as u256;
            assert vm.Peek(1) == if count == 0 then 1 else 0;
            assert vm.Peek(2) == if count == 0 then 1 else 0;
            assert vm.Peek(3) == count;
            assert vm.SlicePeek(0, 4) == Stack.Make([end as u256, if count == 0 then 1 else 0, if count == 0 then 1 else 0, count]);

            assert vm.CodeAtPC() == JUMPI;
            vm := Bytecode.JumpI(vm);
            assert vm.SlicePeek(0, 2) == Stack.Make([if count == 0 then 1 else 0, count]);
        }
        // end of program
        assert vm.CodeAtPC() == JUMPDEST;
        vm := Bytecode.JumpDest(vm);

        assert vm.CodeAtPC() == STOP;
        vm := Stop(vm);
        assert vm.RETURNS?;
    }
}
