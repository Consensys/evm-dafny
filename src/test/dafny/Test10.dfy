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

include "../../dafny/evms/berlin.dfy"

/** Provide some tests to check some qualitative properties of bytecode.
 *
 *  We use an EVM with no gas as the bytecode high-level instructions
 *  like `Push1` do not consume gas.
 */
module Test10 {

    import opened Int
    import opened Bytecode
    import opened EvmBerlin
    import Stack

    /**
    *   A very simple linear program manipulating the stack.
    *
    */
    method {:test} main1()
    {
        // Initialise VM
        var vm := EvmBerlin.InitEmpty(0);

        var a: u8 := 0x01;
        var b: u8 := 0x02;

        ghost var st := vm.GetStack();

        vm := Push1(vm, a);
        vm := Push1(vm, b);
        vm := Add(vm);

        assert vm.Peek(0) as nat == (a + b) as nat;

        vm := Pop(vm);
        assert vm.GetStack() == st;
    }

    /**
     *  A loop.
     *
     *  @param  c   The number of times to iterate the loop.
     */
    method main2(c: u8)
    {
        // Initialise VM
        var vm := EvmBerlin.InitEmpty(0);

        var a: u8 := 0x01;
        var b : u8 := 0x02;
        var count: u8 := c;

        ghost var g := vm.GetStack();

        while count > 0
            invariant vm.IsExecuting()
            invariant vm.GetStack() == g
        {
            vm := Push1(vm, a);
            vm := Push1(vm, b);
            vm := Add(vm);
            vm := Pop(vm);
            count := count - 1 ;
        }
        assert vm.GetStack() == g;
    }

    /**
    *  Refines `main2` by ghosting `count` and storing the corresponding value
    *  on the stack.
    *
    *  @param  c   The number of times to iterate the loop.
    */
    method main3(c: u8)
    {
        var a: u8 := 0x01;
        var b : u8 := 0x02;

        // Initialise VM
        var vm := EvmBerlin.InitEmpty(0);

        vm := Push1(vm, c);
        ghost var g := vm.GetStack();
        ghost var count : u256 := c as u256;

        assert count == vm.Peek(0);

        while vm.Peek(0) > 0
            invariant vm.IsExecuting()
            invariant Stack.Size(vm.GetStack()) > 0
            invariant count == vm.Peek(0)
            invariant vm.GetStack() == Stack.Make([count])
        {
            vm := Push1(vm, a);
            vm := Push1(vm, b);
            vm := Add(vm);
            vm := Pop(vm);

            //  count := count - 1 ;
            vm := Push1(vm, 0x1);
            vm := Swap(vm, 1);
            vm := Sub(vm);
            count := count - 1;
        }
        assert count == 0;
        assert vm.GetStack() == Stack.Make([0]);
    }

    /**
     *  A modular proof. main4a calls main4b
     *
     *  @param  c   The number of times to iterate the loop.
     */
    method main4a(c: u8)
    {
        // Initialise VM
        var vm := EvmBerlin.InitEmpty(0);

        var a: u8 := 0x01;
        var b : u8 := 0x02;
        var count: u8 := c;

        ghost var g := vm.GetStack();

        while count > 0
            invariant vm.IsExecuting()
            invariant vm.GetStack() == g
        {
            vm := main4b(vm);
            count := count - 1 ;
        }
        assert vm.GetStack() == g;
    }

    /** This method performs  an addition 0x1 + 0x2 and leaves the stack unchanged.  */
    method main4b(v: EvmState.State) returns (v': EvmState.State)
        requires v.IsExecuting()
        requires v.Capacity() >= 2
        ensures v'.IsExecuting() && v'.GetStack() == v.GetStack()
    {
        v':= v;
        v' := Push1(v', 0x1);
        v' := Push1(v', 0x2);
        v' := Add(v');
        v' := Pop(v');
    }

    /**
    *  Refines `main3` and compute the condition of the loop using the stack
    *  and the comparisons operators.
    *
    *  @param  c   The number of times to iterate the loop.
    */
    method main5(c: u8)
    {
        // Initialise VM
        var vm := EvmBerlin.InitEmpty(0);

        var a: u8 := 0x01;
        var b : u8 := 0x02;

        vm := Push1(vm, c);
        ghost var g := vm.GetStack();
        ghost var count := c as u256;

        assert vm.GetStack() == Stack.Make([count]);

        //  compute count > 0

        //  top of the stack has the result of count > 0
        //  push 0, then duplicate second element on top
        vm := Push1(vm, 0x0);
        vm := Dup(vm, 2);
        assert vm.GetStack() == Stack.Make([count, 0, count]);

        //  compute stack[0] > stack[1]
        vm := Gt(vm);
        assert vm.GetStack() == Stack.Make([if count > 0 then 1 else 0, count]);

        assert count == vm.Peek(1);

        while vm.Peek(0) > 0
            invariant vm.IsExecuting()
            invariant Stack.Size(vm.GetStack()) == 2
            invariant count == vm.Peek(1)
            invariant count == vm.Peek(1) >= 0
            invariant vm.Peek(0) > 0 <==> count > 0

            decreases count
        {
            //  top of the stack is the last result of stack[0] > stack[1]
            vm := Pop(vm);
            assert vm.GetStack() == Stack.Make([count]);

            //  a + b and discard result
            vm := Push1(vm, a);
            vm := Push1(vm, b);
            vm := Add(vm);
            vm := Pop(vm);

            assert count == vm.Peek(0) ;
            assert count > 0;
            //  count := count - 1 ;
            vm := Push1(vm, 0x1);
            vm := Swap(vm, 1);
            assert vm.GetStack() == Stack.Make([count, 1]);

            vm := Sub(vm);
            assert vm.GetStack() == Stack.Make([count - 1]);

            //  prepare comparison count > 0. count is at the top
            vm := Push1(vm, 0x0);
            vm := Dup(vm, 2);
            assert vm.GetStack() == Stack.Make([count - 1, 0, count - 1]);

            //  compute stack[0] > stack[1]
            vm := Gt(vm);
            assert vm.GetStack() == Stack.Make([if count - 1 > 0 then 1 else 0, count - 1]);
            count := count - 1;
        }
        assert count == vm.Peek(1);
        vm := Pop(vm);
        assert count == vm.Peek(0);
        assert count == 0;
        assert Stack.Size(vm.GetStack()) == 1;
        assert vm.GetStack() == Stack.Make([0]);
    }

}
