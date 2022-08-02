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

include "../../dafny/evm.dfy"
include "../../dafny/evms/berlin.dfy"

import opened Int
import opened Opcode
import opened Bytecode

// Arbitrary limit for now
const GASLIMIT : nat := 100;

/**
 *   A very simple program manipulating the stack.
 *
 */
method {:test} main1()
{
    // Initialise Bytecode
    var tx := Context.Create(0xabc,0xdef,0,[],0);
    var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[]);

    var a: u8 := 0x01;
    var b: u8 := 0x02;

    ghost var g := vm.GetStack();

    vm := Push1(vm, a);
    vm := Push1(vm, b);
    vm := Add(vm);

    assert vm.Peek(0) as nat == (a + b) as nat;

    vm := Pop(vm);
    assert vm.GetStack() == g;
}

/**
 *  A loop.
 */
method main2(c: u8)
{
    // Initialise Bytecode
    var tx := Context.Create(0xabc,0xdef,0,[],0);
    var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[]);
    var a: u8 := 0x01;
    var b : u8 := 0x02;
    var count: u8 := c;

    ghost var g := vm.GetStack();

    while count > 0
        invariant !vm.IsFailure()
        invariant  vm.GetStack() == g
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
 *  Compute cout := count - 1 with the stack.
 *  In this first implementation we use a variant of SUB, subR
 *  that computes stack1 - stack0 instead of stack0 - stack1.
 */
method main3(c: u8)
{
    var a: u8 := 0x01;
    var b : u8 := 0x02;

    // Initialise Bytecode
    var tx := Context.Create(0xabc,0xdef,0,[],0);
    var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[]);

    vm := Push1(vm, c);
    ghost var g := vm.GetStack();
    ghost var count : u256 := c as u256;

    assert count == vm.Peek(0);

    while vm.Peek(0) > 0
        invariant !vm.IsFailure()
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
 *  Test top of stack with LT/GT
 *  instead of count > 0.
 */
method main5(c: u8)
{
    // Initialise Bytecode
    var tx := Context.Create(0xabc,0xdef,0,[],0);
    var vm := EvmBerlin.Create(tx,map[],GASLIMIT,[]);

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
        invariant !vm.IsFailure()
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
