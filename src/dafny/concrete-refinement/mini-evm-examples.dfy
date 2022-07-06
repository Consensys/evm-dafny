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

include "../evms/mini-evm-with-gas.dfy"  

/**
 *   A very simple program manipulating a stack.
 */
method main1() 
{
    var e := new EVM(0, false);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    ghost var g := e.stack;

    e.push(a); 
    e.push(b);
    e.add();

    assert e.stack[0] == a + b; 

    e.pop();
    assert e.stack == g;
}

/**
 *  A loop.
 */
method main2(c: uint256) 
{
    var e := new EVM(0, false);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;
    var count: uint256 := c;

    ghost var g := e.stack;

    while count > 0 
        invariant  e.stack == g
    {
        e.push(a);
        e.push(b);
        e.add();
        e.pop();
        count := count - 1 ;
    }
    
    assert e.stack == g;
}

/**
 *  Compute cout := count -1 with the stack.
 *  In this first implementation we use a variant of SUB, subR
 *  that computes stack1 - stack0 instead of stack0 - stack1.
 */
method main3(c: uint256) 
{
    var e := new EVM(0, false);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    e.push(c);
    ghost var g := e.stack;
    ghost var count := c;

    assert count == e.stack[0];

    while e.stack[0] > 0 
        invariant  |e.stack| > 0  
        invariant count == e.stack[0]
        invariant e.stack == [count]
    {
        e.push(a);
        e.push(b);
        e.add();
        e.pop();

        //  count := count - 1 ;
        e.push(0x1);
        e.subR();
        count := count - 1;
        
    }
    assert count == 0;
    assert e.stack == [0];
}

/**
 *  Add swap1 instructin and use real semantics for SUB.
 */
method main4(c: uint256)  
{
    var e := new EVM(0, false);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    e.push(c);
    ghost var g := e.stack;
    ghost var count := c;

    assert count == e.stack[0];

    while e.stack[0] > 0 
        invariant  |e.stack| > 0  
        invariant count == e.stack[0]
    {
        e.push(a);
        e.push(b);
        e.add();
        e.pop();

        //  count := count - 1 ;
        e.push(0x1);
        e.swap1();
        e.sub();

        count := count - 1;
        
    }
}

/**
 *  Test top of stack with LT/GT
 *  instead of count > 0.
 */
method main5(c: uint256)  
{
    var e := new EVM(0, false);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    e.push(c);
    ghost var g := e.stack;
    ghost var count := c;

    //  stack = [count]
    assert count == e.stack[0];

    //  compute count > 0 

    //  top of the stack has the result of count > 0
    //  push 0, then duplicate second element on top
    e.push(0x0);
    e.dup2();
    //  stack = [count, 0, count]
    //  compute stack[0] > stack[1]
    e.gt();
    //  stack = [count > 0, count]

    assert(count == e.stack[1]); 

    while e.stack[0] > 0 
        invariant  |e.stack| > 1  
        invariant count == e.stack[1] >= 0
        invariant e.stack[0] > 0 <==> count > 0
        invariant |e.stack| == 2

        decreases count
    {
        //  top of the stack is the last result of stack[0] > stack[1]
        e.pop();
        //  stack = [count] 
        //  a + b and discard result
        e.push(a);
        e.push(b);
        e.add();
        e.pop();

        assert count == e.stack[0] ;
        assert count > 0;
        //  count := count - 1 ;
        e.push(0x1);
        e.swap1();
        //  stack = [count, 1]
        e.sub();
        //  stack = [count - 1]

        //  prepare comparison count > 0. count is at the top
        e.push(0x0);
        e.dup2();
        //  stack = [count - 1, 0, count - 1]
        //  compute stack[0] > stack[1]
        e.gt();        
        //  stack = [count - 1 > 0, count - 1]
        count := count - 1;
        
    }
    assert count == e.stack[1];
    e.pop();
    assert e.stack[0] == count;
    assert count == 0;
    assert |e.stack| == 1;
    assert e.stack == [0];

}

/**
 * Use gas cost.
 */
method main6(c: uint256, g: uint256)  
{
    var e := new EVM(0, false);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    e.push(c);
    ghost var g := e.stack;
    ghost var count := c;

    //  stack = [count]
    assert count == e.stack[0];

    //  compute count > 0 

    //  top of the stack has the result of count > 0
    //  push 0, then duplicate second element on top
    e.push(0x0);
    e.dup2();
    //  stack = [count, 0, count]
    //  compute stack[0] > stack[1]
    e.gt();
    //  stack = [count > 0, count]

    assert(count == e.stack[1]); 

    while e.stack[0] > 0 
        invariant  |e.stack| > 1  
        invariant count == e.stack[1] >= 0
        invariant e.stack[0] > 0 <==> count > 0
        invariant |e.stack| == 2

        decreases count
    {
        //  top of the stack is the last result of stack[0] > stack[1]
        e.pop();
        //  stack = [count] 
        //  a + b and discard result
        e.push(a);
        e.push(b);
        e.add();
        e.pop();

        assert count == e.stack[0] ;
        assert count > 0;
        //  count := count - 1 ;
        e.push(0x1);
        e.swap1();
        //  stack = [count, 1]
        e.sub();
        //  stack = [count - 1]

        //  prepare comparison count > 0. count is at the top
        e.push(0x0);
        e.dup2();
        //  stack = [count - 1, 0, count - 1]
        //  compute stack[0] > stack[1]
        e.gt();        
        //  stack = [count - 1 > 0, count - 1]
        count := count - 1;
        
    }
    assert count == e.stack[1];
    e.pop();
    assert e.stack[0] == count;
    assert count == 0;
    assert |e.stack| == 1;
    assert e.stack == [0];

}

