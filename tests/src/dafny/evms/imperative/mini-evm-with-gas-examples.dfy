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

include "../../../../../src/dafny/evms/imperative/mini-evm-with-gas.dfy"     
include "../../../../../src/dafny/util/int.dfy"

import opened Int

/**
 *   A very simple program manipulating the stack.  
 */
method main1(g: u256)  
    requires g >= 4 
{
    var e := new EVMI(g, true);  
    var a: u8 := 0x01;
    var b : u8 := 0x02;

    ghost var g := e.stack;

    e.push(a);
    e.push(b);
    e.add(); 

    assert e.stack[0] == (a + b) as u256;

    e.pop();
    assert e.stack == g; 
    assert e.gas >= 0;
}

/**
 *  A loop.
 */
method main2(c: u256, g: u256) 
    requires g as nat >= c as nat * 4
{
    //  The pre-condition constrains input c
    assert c as nat * 4 <= MAX_U256;
    var e := new EVMI(g, true);
    var a: u8 := 0x01;
    var b : u8 := 0x02;
    var count: u256 := c;

    ghost var s := e.stack;

    while count > 0 
        invariant  e.stack == s
        invariant e.gas  >= count * 4
    {
        e.push(a);
        e.push(b);
        e.add();
        e.pop();
        count := count - 1 ;
    }
    assert e.gas >= 0 ;
    assert e.stack == s;
}

/**
 *  Add swap1 instructin and use real semantics for SUB.
 */
method main4(c: u8, g: u256)  
    requires g as nat >= 1 + c as nat * 7
{
    var e := new EVMI(g, true);
    var a: u8 := 0x01;
    var b : u8 := 0x02;

    e.push(c);
    ghost var count := c as u256;

    assert count == e.stack[0];

    while e.stack[0] > 0 
        invariant  |e.stack| > 0  
        invariant count == e.stack[0]
        invariant e.gas >= count * 7
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
    assert e.gas >= 0;
}

/**
 *  Test top of stack with LT/GT
 *  instead of count > 0.
 */
method main5(c: u8, g: u256)  
    requires g as nat >= 5 + 11 * c as nat
{
    var e := new EVMI(g, true);
    var a: u8 := 0x01;
    var b : u8 := 0x02;

    e.push(c);
    ghost var count := c as u256;

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
        invariant e.gas >= 1 + 11 * count 

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
    assert e.gas >= 0;

}

/**
 *  Enable gas cost.
 */
method main6(c: u8, g: u256) 
    requires g as nat >= 5 + 11 * c as nat  
{
    var e := new EVMI(g, true);
    var a: u8 := 0x01;
    var b : u8 := 0x02;

    e.push(c);
    ghost var g := e.stack;
    ghost var count := c as u256;

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
        invariant e.gas >= 1 + 11 * count

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
    assert e.gas >= 0;

}

/**
 *  Compute c in a loop.
 */
method foo(c: u8) returns (i: u256)
    ensures i == fooSpec(c as u256) 
{
    i := 0;
    var c' := c;

    while c' > 0 
        invariant c' as nat + i as nat == c as nat  
    {
        i := i + 1;
        c' := c' - 1;
    }
    assert i == c as u256;

}

/**
 *  Compute c in a loop.
 */
method foo2(c: u8, g: u256) returns (ghost i: u256)
    requires g as nat >= 2 + 7 * c as nat  
    ensures i == c as u256
{
    i := 0;
    ghost var c' := c as u256;

    var e := new EVMI(g, true);

    e.push(c);
    assert e.stack[0] == c as u256 == c';

    //  push i
    assert e.gas >= 1;
    e.push(0x0);

    while e.stack[1] > 0
        invariant |e.stack| > 1
        invariant c' == e.stack[1]
        invariant i == e.stack[0]
        invariant c' as nat + i as nat == c as nat  
        invariant e.gas >= 7 * c'
    {
        i := i + 1;
        //  compute i + 1
        e.push(0x01);
        e.add();

        //  i + 1 is at top opf the stack 

        c' := c' - 1;
        //  compute c' update on the stack
        e.swap1();
        //  c' is at top of stack
        e.push(0x1);
        e.swap1();
        e.sub();
        //  e.stack[0] should contain c'
        assert e.stack[0] == c';
        e.swap1();
    }
}

/**
 *  Compute c in a loop.
 */
method foo3(c: u8, e: EVMI) 
    requires !e.checkCode
    requires e.checkGas && e.gas as nat >= 2 + 7 * c as nat 
    ensures |e.stack| > 0 && e.stack[0] == fooSpec(c as u256) as u256

    modifies e
{
    //  original algorithm variables become verification/ghost variable 
    ghost var i := 0;
    ghost var c' := c as u256;

    e.push(c);
    assert e.stack[0] == c as u256 == c';

    //  push i
    e.push(0x0);

    while e.stack[1] > 0
        invariant |e.stack| > 1
        //  locate original variables in the stack
        invariant c' == e.stack[1]
        invariant i == e.stack[0]
        invariant e.gas >= 7 * c'
        invariant c' as nat + i as nat == c as nat  
    {
        i := i + 1;
        //  compute i + 1
        e.push(0x01);
        e.add();
        //  i + 1 is at top of the stack 

        c' := c' - 1;
        //  compute c' update on the stack
        e.swap1();
        //  c' is at top of stack
        e.push(0x1);
        e.swap1();
        e.sub();
        //  e.stack[0] should contain c'
        assert e.stack[0] == c';
        e.swap1();
    }
}

/**
 *  Pass parameter on stack
 */
// method foo4(e: EVM) 
//     requires |e.stack| > 0 
//     requires e.checkGas && e.gas as nat >= 2 + 10 * e.stack[0] as nat 
//     ensures |e.stack| > 0 && e.stack[0] == fooSpec(e.stack[0]) as u256
//     ensures e.stack[1..] == old(e.stack[1..])

//     modifies e
// {
//     //  original algorithm variables become verification/ghost variable 
//     ghost var i := 0;
//     ghost var c := e.stack[0];
//     ghost var c' := e.stack[0];
//     // e.push(c);
//     assert e.stack[0] == c' == c;

//     //  push i
//     e.push(0x00); 
//     //  [i, c' , -]
//     ghost var oldS := e.stack[2..];

//     while e.stack[1] > 0
//         invariant |e.stack| > 1
//         //  locate original variables in the stack
//         invariant c' == e.stack[1]
//         invariant i == e.stack[0]
//         invariant e.gas >= 1 + 10 * c'
//         invariant e.stack[2..] == oldS
//         invariant c' as nat + i as nat == c as nat  
//     {
//         // assume e.stack[2..] == oldS;
//         //  [i, c', -]
//         i := i + 1;
//         //  compute i + 1
//         e.incr(0, 0x01);
//         //  [i + 1, i, c', -]
//         // assert e.stack[3..] == oldS;
//         e.swap1(); 
//         //  [i, i + 1, c', -]
//         e.pop();
//         //  [i + 1, c', -]
//         //  i + 1 is at top of the stack 
//         assert e.stack[2..] == oldS;
//         //  compute c' update on the stack
//         e.swap1();
//         assert e.stack[0] == c';
//         c' := c' - 1;
//         assert e.stack[0] == c' + 1;
//         //  [ c', i, -] 
//         //  c' is at top of stack
//         e.push(0x1);
//         assert e.stack[3..] == oldS; 
//         e.swap1();
//         assume e.stack[0] >= e.stack[1];
//         e.sub();
//         //  [ c' - 1, i + 1, -]
//         //  e.stack[0] should contain c'
//         assert e.stack[0] == c';
//         e.swap1();
//         //  [ i + 1, c' - 1, -]
//         assert e.stack[2..] == oldS;
//     }
//     e.pop();
// }

lemma foobar(xa: seq<u256>)
    requires |xa| > 0
    ensures old(xa)[1..] == old(xa[1..])
{
    
}

/**
 *  Functional spec of foo
 */
 function fooSpec(c: u256) : u256
 {
    c
 }

method main101(e: EVMI, e2: EVMI) 
    // requires |e.stack| > 0  
    requires e.gas as nat >= 3
    requires !e.checkCode
    // ensures |e.stack| > 0 && e.stack[0] == fooSpec(e.stack[0])
    // ensures e.stack[1..] == old(e.stack[1..])

    modifies e
{
    e.push(0x01);
    e.push(0x02);
    e.add();
 
    
    assert e.stack[0] == 3;
}
