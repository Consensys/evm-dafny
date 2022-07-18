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

include "../../util/int.dfy"
include "../EVMOpcodes.dfy"

include "../functional/evm.dfy"  

import opened Int
import opened EVMOpcodes
import EVMF = EVM 

/** An OO version of the EVM.
 * 
 *  @note   The stack can contain at most 1024 items which is not captured
 *          by this type definition. 
 *  @note   This EVM supports interpretation of EVM-IR (using while loops, if-then-else)
 *          as well as raw bytecode. 
 */
type EVMStack = seq<u256>

/** 
 *  Provide an initialiased EVM with a small instruction set.
 *  Gas can be enabled or disabled.
 */
class EVMI {  

    /** The stack of this VM. */
    var stack: EVMStack

    /** The gas left in this EVM.  */
    var gas: u256

    /** The program counter, if interpreting bytecode. */
    var pc: nat

    /** Enable/disable gas check. */
    const checkGas: bool

    /** Enable/disable bytecode checking. */
    const checkCode: bool

    /** The optional (can be empty sequence) bytecode. */
    const code: seq<u8>

    const ctx := Context.Context(0, 0, 0, [])
    const eevm :EVMF.T := EVMF.create(Context.Context(0, 0, 0, []), map[], 0 as nat, [])

    /** Init the VM. 
     *  
     *  @param  g       Initial gas in the EVM.add
     *  @param  check   Whether the machine requires gas or not.
     *  @param  c       The bytecode.
     *  @param  checkB  Whether to check the bytecode (useful for refinement proofs).
     *
     *
     *  @note           If bytecode not empty, every execution of an instruction
     *                  is checked against the bytecode.
     *  @example        c = [PUSH1, 2]
     *                  this.push(v) can only be executed if current pc is such that code[pc] is PUSH1
     *                  and code[pc + 1] == v 
     */
    constructor (g: u256, check: bool, c: seq<u8> := [], check': bool := false) 
        requires |c| <= MAX_U256
        ensures stack == []
        ensures gas == g 
        ensures checkGas == check
        ensures pc == 0
        ensures checkCode == check'
        ensures code == c
        ensures gas as nat == EVMF.create(Context.Context(0, 0, 0, []), map[], g as nat, []).gas
        ensures Stack.Stack(stack) == EVMF.create(ctx, map[], g as nat, c).stack
        ensures Code.Code(c) == EVMF.create(ctx, map[], g as nat, c).code
        // ensures pc as u256 == EVMF.create(ctx, map[], g as nat, c).pc
    {
        pc := 0;
        stack := []; 
        gas := g;
        checkGas := check;
        code := c;
        checkCode := check';
    }

    //  The semantics of the following instructions are defined by their pre- and post-conditions.
    //  One pre-condition checks for gas availability and can be disabled by turning the
    //  `checkGas` flag off. The code check can also be turned off.
    
    /** 
     *  PUSH1 opcode.
     *
     *  @param  v   The value to push on the stack.
     *  @return     Add `v` to the top of the stack (and convert to u256).
     */
    method push(v: u8, ghost evmf: EVMF.T := eevm) 
        requires !checkGas || gas >= 1
        requires !checkCode || (pc + 1 < |code| && code[pc] == PUSH1 && code[pc + 1] == v) 
        ensures |stack| == |old(stack)| + 1
        ensures stack == [v as u256] + old(stack)
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(pc) + 2
        modifies this 
    {
        stack := [v as u256] + stack;
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
        requires stack[0] as nat + stack[1] as nat <= MAX_U256
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
     *  Siganture is: JUMPI destination condition
     */
    method jumpi()  
        requires |stack| >= 2
        requires !checkGas || gas >= 1
        requires !checkCode || (pc < |code| && code[pc] == JUMPI) 

        ensures |stack| == |old(stack)| - 2
        ensures stack == old(stack)[2..]
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == if old(stack[1]) != 0 then old(stack[0]) as nat else old(pc) as nat  + 1 

        modifies this
    {
        pc := if stack[1] != 0 then stack[0] as nat else pc + 1 ;
        stack := stack[2..];
        gas := gas - (if checkGas then 1 else 0);
    }

    /**
     *  JUMP instruction.
     *  Jumps to the instruction `a` where `a` is the value at the top of the stack.
     */
    method jump()  
        requires |stack| >= 1
        requires !checkGas || gas >= 1
        requires !checkCode || (pc as nat < |code| && code[pc] == JUMP) 

        ensures |stack| == |old(stack)| - 1
        ensures stack == old(stack)[1..]
        ensures !checkGas || gas == old(gas) - 1
        ensures pc == old(stack[0]) as nat

        modifies this
    {
        pc := stack[0] as nat;
        stack := stack[1..];
        gas := gas - (if checkGas then 1 else 0);
    }

    /**
     *  Replaces the top of stack `t` by the status `t == 0`.
     */
    method iszero()  
        requires pc as nat < MAX_U256
        requires |code| <= MAX_U256
        requires |stack| >= 1
        requires !checkGas || gas >= 1
        requires !checkCode || (pc as nat < |code| && code[pc] == ISZERO) 

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

    /**
     *  Terminates the program.
     *  @todo   Check that this is what STOP does. 
     */
    method stop()  
        requires !checkGas || gas >= 1
        requires !checkCode || (pc as nat < |code| && code[pc] == STOP) 

        ensures |stack| == |old(stack)|
        ensures !checkGas || gas == old(gas) - 1
        // ensures pc == old(pc) + 1 

        modifies this
    {
        gas := gas - (if checkGas then 1 else 0);
    }

}
