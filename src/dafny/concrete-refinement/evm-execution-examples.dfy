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

import opened EVMOpcodes

/**
 *  State relation for two evms.
 *  Ignore pc. 
 */
predicate equiv(e1: EVM, e2: EVM) 
    reads e1, e2
{
    && e1.stack == e2.stack
    && e1.gas >= e2.gas 
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
method main1(g: uint256) 
    requires g >= 5
{
    //  EVM #1
    var e1 := new EVM(g, true); 
    var a: uint8 := 0x01;
    var b : uint8 := 0x02;

    //  EVM #2
    var e2 := new EVM(g, true, [PUSH1, 1, PUSH1, 2, ADD, POP, STOP]);
    
    ghost var g := e1.stack;

    //  First check 
    assert equiv(e1, e2); 

    e2.push(a);
    e1.push(a);
    assert equiv(e1, e2);
 
    e2.push(b); 
    e1.push(b);
    assert equiv(e1, e2);
    
    e2.add();
    e1.add();  
    assert equiv(e1, e2);

    assert e1.stack[0] == a as uint256 + b as uint256;
    assert e2.stack[0] == a as uint256 + b as uint256;

    e2.pop();
    e1.pop();
    assert equiv(e1, e2); 

    e2.stop();
    // e1 chooses not to do anything
    assert equiv(e1, e2); 

    assert e1.stack == g;
    assert e1.gas >= 0;

    assert e2.stack == g;
    assert e2.gas >= 0;
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
 *  
 */
method main5(c: uint8)  
{
    var end : uint8 := 16;

    var e := new EVM(0, false,
        // []
        [
            PUSH1, c,       //  0
            DUP1,           //  2
            ISZERO,         //  3
            DUP1,           //  4
            PUSH1, end,     //  5
            JUMPI,          //  7
            POP,            //  8
            PUSH1, 1,       //  9
            SWAP1,          // 11
            SUB,            // 12
            PUSH1, 2,       // 14 
            JUMP,           // 15
            STOP            // 16
        ]
        );
    var a: uint8 := 0x01;
    var b : uint8 := 0x02;

    ghost var g := e.stack;
    ghost var count :uint256 := c as uint256;

    //  push input on the stack
    e.push(c);  // [count]
    assert count == e.stack[0];
  
    // Compute result of test c > 0
    e.dup1();   // [count, count]
    e.iszero(); // [count == 0, count]
    e.dup1();   // [count == 0, count == 0, count]
    //  if count == 0 jump to end 
    e.push(end);  // [end, count == 0, count == 0, count]
    e.jumpi();  // [count == 0, count]
    assert count == e.stack[1];

    //  this test/while loop is in main5 only, not in the bytecode.
    //  it corresponds to P1 choosing its strategy to match the bytecode.
    while e.stack[0] == 0   
        invariant  |e.stack| > 1  
        invariant count == e.stack[1]
        invariant count == 0 <==> e.stack[0] > 0 
        invariant e.stack[0] == 0 <==> e.pc == 8
        invariant e.stack[0] > 0 <==> e.pc == 16
        decreases count
    {
        assert e.pc == 8;
        //  [count == 0, count]
        e.pop();        // [count]
        e.push(0x1);    // [1, count]
        e.swap1();      // [count, 1]
        e.sub();        // [count - 1] 
        //  jump to 2   
        e.push(2); // [2, count - 1]
        e.jump();       // [count - 1]

        // Compute result of test c > 0, same as before the loop.
        e.dup1();       // [count - 1, count - 1]
        e.iszero();     // [count == 0, count]
        e.dup1();       // [count == 0, count == 0, count]
        //  if count == 0 jump to end 
        e.push(end);    // [end, count == 0, count == 0, count]
        e.jumpi();      // [count == 0, count]
        count := count - 1;
    }
    // end of program
    e.stop();
}
