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

include "../utils/NativeTypes.dfy"
include "../utils/NonNativeTypes.dfy"
include "./EVMOpcodes.dfy"

import opened NativeTypes
import opened NonNativeTypes
import opened EVMOpcodes

/** The type for the EVM stack. 
 * 
 *  @note   The stack can contain at most 1024 items which is not captured
 *          by this type definition. 
 */
type EVMStack = seq<uint256>

/** 
 *  Provide an initialiased EVM with a small instruction set.
 *  Gas can be enabled or disabled.
 */
class EVM {

    /** The stack of the VM. */
    var stack: EVMStack

    /** The gas left in the EVM.  */
    var gas: uint256

    /** The program counter. */
    var pc: nat 

    /** Enable/disable gas check. */
    const checkGas: bool

    /** Enable/disable bytecode checking. */
    const checkCode: bool

    /** The optional (can be empty sequence) bytecode. */
    const code: seq<uint8>

    /** Init the VM. 
     *  
     *  @param  g       Initial gas in the EVM.add
     *  @param  check   Whether the machine requires gas or not.
     *  @param  c       The bytecode.
     *
     *  @note           If bytecode not empty, every execution of an instruction
     *                  is checked against the bytecode.
     *  @example        c = [PUSH1, 2]
     *                  this.push(v) can only be executed if current pc is such that code[pc] is PUSH1
     *                  and code[pc + 1] == v 
     */
    constructor (g: uint256, check: bool, c: seq<uint8> := []) 
        ensures stack == []
        ensures gas == g 
        ensures checkGas == check
        ensures pc == 0
        ensures checkCode == (|c| > 0)
        ensures code == c
    {
        pc := 0;
        stack := []; 
        gas := g;
        checkGas := check;
        code := c;
        checkCode := |c| > 0;
    }

    //  The semantics of the following instructions are
    //  defined by their pre- and post-conditions.

    /** 
     *  PUSH1 opcode.
     *
     *  @param  v   The value to push on the stack.
     *  @return     Add `v` to the top of the stack (and convert to uint256).
     */
    method push(v: uint8) 
        requires !checkGas || gas >= 1
        requires !checkCode || (pc + 1 < |code| && code[pc] == PUSH1 && code[pc + 1] == v) 
        ensures |stack| == |old(stack)| + 1
        ensures stack == [v as uint256] + old(stack)
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 2

        modifies this
    {
        stack := [v as uint256] + stack;
        gas := gas - (if checkGas then 1 else 0);
        pc := pc + 2;
    }

    /**
     *  POP opcode.
     */
    method pop() 
        requires |stack| > 0 
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == POP) 

        ensures |stack| == |old(stack)| - 1
        ensures stack == old(stack[1..])
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 1

        modifies this
    {
        stack := stack[1..];
        gas := gas - (if checkGas then 1 else 0);
        pc := pc + 1;
    }

    /**
     *  SWAP1 opcode.
     */
    method swap1()  
        requires |stack| >= 2
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == SWAP1) 

        ensures |stack| == |old(stack)|
        ensures stack[0] == old(stack[1])
        ensures stack[1] == old(stack[0])
        ensures stack[2..] == old(stack[2..])
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 1

        modifies this
    {
        stack := [stack[1]] + [stack[0]] + stack[2..];
        gas := gas - (if checkGas then 1 else 0);
        pc := pc + 1;
    }


    /**
     *  ADD opcode.
     */
    method add()  
        requires |stack| >= 2
        requires stack[0] as nat + stack[1] as nat <= MAX_UINT256
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == ADD) 

        ensures |stack| == |old(stack)| - 1
        ensures stack[0] == old(stack)[0] + old(stack)[1]
        ensures stack[1..] == old(stack[2..])
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 1

        modifies this
    {
        stack := [stack[0] + stack[1]] + stack[2..];
        gas := gas - (if checkGas then 1 else 0);
        pc := pc + 1;
    }

    /**
     *  SUB opcode. compute stack[1] - stack[0], which is not the semantics
     *  of SUB that is stack[0] - stack[1]
     */
    // method subR()  
    //     requires |stack| >= 2
    //     requires stack[1] as nat - stack[0] as nat >= 0
    //     requires !checkGas || gas >= 1

    //     ensures |stack| == |old(stack)| - 1
    //     ensures stack[0] == old(stack)[1] - old(stack)[0]
    //     ensures stack[1..] == old(stack)[2..]
    //     ensures !checkGas || gas == old(gas) - 1

    //     modifies `stack, `gas
    //     // modifies if checkGas then {`stack, `gas} else {this`stack} 
    // {
    //     stack := [stack[1] - stack[0]] + stack[2..];
    //     gas := gas - (if checkGas then 1 else 0);
    // }

    /**
     *  SUB opcode. compute stack[0] - stack[1], which is the
     *  real semantics of sub 
     *
     *  Assume stack = [a, b] + xr
     *  @returns [a - b] + xr
     */
    method sub()  
        requires |stack| >= 2
        requires stack[0] as nat - stack[1] as nat >= 0
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == SUB) 

        ensures |stack| == |old(stack)| - 1
        ensures stack[0] == old(stack)[0] - old(stack)[1]
        ensures stack[1..] == old(stack)[2..]
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 1

        modifies this 
    {
        stack := [stack[0] - stack[1]] + stack[2..];
        gas := gas - (if checkGas then 1 else 0);
        pc := pc + 1;
    }
    /**
     *  DUP1 opcode. Duplicate the second element of the stack.
     */
    method dup1()  
        requires |stack| >= 1
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == DUP1) 

        ensures |stack| == |old(stack)| + 1
        ensures stack == [old(stack)[0]] + old(stack)
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 1

        modifies this
    {
        stack := [stack[0]] + stack;
        gas := gas - (if checkGas then 1 else 0);
        pc := pc + 1;
    }


    /**
     *  DUP2 opcode. Duplicate the second element of the stack.
     */
    method dup2()  
        requires |stack| >= 2
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == DUP2) 

        ensures |stack| == |old(stack)| + 1
        ensures stack == [old(stack)[1]] + old(stack)
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 1

        modifies this
    {
        stack := [stack[1]] + stack;
        gas := gas - (if checkGas then 1 else 0);
        pc := pc + 1;
    }

    /**
     *  DUPi opcode. Duplicate the i-th element of the stack.
     *  
     *  @param  i   The index of the element.
     *  Assume  stack
     *  @returns [stack[i]] + stack
     */
    // method dup(i: nat)
    //     requires 0 <= i <= 15  
    //     requires |stack| > i as nat
    //     requires !checkGas || gas >= 1
    //     requires !checkCode || (pc < |code| && code[pc] == 0x07) 

    //     ensures |stack| == |old(stack)| + 1
    //     ensures stack == [old(stack)[i]] + old(stack)
    //     ensures !checkGas || gas == old(gas) - 1
    //     ensures pc == old(pc) + 1

    //     modifies this
    // {
    //     stack := [stack[i]] + stack;
    //     gas := gas - (if checkGas then 1 else 0);
    //     pc := pc + 1;
    // }

    /**
     *  GT opcode. Compute stack[0] > stack[1] and store result. 
     */
    method gt()  
        requires |stack| >= 2
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == GT) 

        ensures |stack| == |old(stack)| - 1
        ensures stack == [if (old(stack)[0] > old(stack)[1]) then 1 else 0] + old(stack)[2..]
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 1 

        modifies this
    {
        stack := (if (stack[0] > stack[1]) then [1] else [0]) + stack[2..];
        gas := gas - (if checkGas then 1 else 0);
        pc := pc + 1;
    }

    /**
     *  JUMPI opcode.
     *  JUMPI uses the top of the stack to determine where to branch.
     *  JUMPI destination condition
     */
    method jumpi()  
        requires |stack| >= 2
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == JUMPI) 

        ensures |stack| == |old(stack)| - 2
        ensures stack == old(stack)[2..]
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == if old(stack[1]) != 0 then old(stack[0]) as nat else old(pc) + 1 

        modifies this
    {
        pc := if stack[1] != 0 then stack[0] as nat else pc + 1 ;
        stack := stack[2..];
        gas := gas - (if checkGas then 1 else 0);
    }

    method jump()  
        requires |stack| >= 1
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == JUMP) 

        ensures |stack| == |old(stack)| - 1
        ensures stack == old(stack)[1..]
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(stack[0]) as nat

        modifies this
    {
        pc := stack[0] as nat ;
        stack := stack[1..];
        gas := gas - (if checkGas then 1 else 0);
    }

    method iszero()  
        requires |stack| >= 1
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == ISZERO) 

        ensures |stack| == |old(stack)|
        ensures stack == [if old(stack[0]) == 0 then 1 else 0] + old(stack[1..])
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 1 
        ensures stack[0] > 0 <==> old(stack[0]) == 0

        modifies this
    {
        pc := pc + 1 ;
        stack := [if stack[0] == 0 then 1 else 0] + stack[1..];
        gas := gas - (if checkGas then 1 else 0);
    }

    method stop()  
        // requires |stack| >= 1
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == STOP) 

        ensures |stack| == |old(stack)|
        // ensures stack == [if old(stack[0]) == 0 then 1 else 0] + old(stack[1..])
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 1 
        // ensures stack[0] > 0 <==> old(stack[0]) == 0

        modifies this
    {
        pc := pc + 1 ;
        // stack := [if stack[0] == 0 then 1 else 0] + stack[1..];
        gas := gas - (if checkGas then 1 else 0);
    }

    //  Macros

    /** Increment a counter. 
     *  
     *  @param  i   An index 0 = top.
     *  @param  v   Value to add to stack[i]
     *
     *  @returns    
     *  Counter must be one of the last 16 items pushed on the stack.
     *  
     */
    // method incr(i: nat, v: uint256)
    //     requires 0 <= i <= 15
    //     requires !checkGas || gas >= 3
    //     requires |stack| > i as nat
    //     requires stack[i] as nat + v as nat <= MAX_UINT256 
    //     requires !checkCode
    //     ensures |stack| == |old(stack)| + 1
    //     ensures stack == [old(stack[i]) + v] + old(stack)
    //     ensures stack[1..] == old(stack)
    //     ensures !checkGas || gas == old(gas) - 3

    //     modifies this
    // {
    //     //  Stack is [x_0, x_1, ..., x _i] + xs
    //     //  put element i on top of stack
    //     dup(i);
    //     //  Stack is [x_i, x_0, x_1, ..., x _i] + xs
    //     push(v);
    //     // Stack is [v, x_i, x_0, x_1, ..., x _i] + xs
    //     add();
    //     // Stack is [x_i + v, x_0, x_1, ..., x _i] + xs
    // }

}
