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

include "./evm-abstract.dfy"

module EVM_BERLIN refines EVM { 

    /** Gas cost map. */
    const gas: map<u8, State -> nat> := map[
        STOP := (_ => 2),
        PUSH1 := (s:State) => (if !s.IsFailure() then (if s.evm.pc == 2 then 3 else 4) else 0)
    ]

    /** Semantics map. */
    const semantics: map<u8, State -> State> := map[
        STOP := (s:State) => Stop(s)
        // PUSH1 := (s:State) =>   if !s.isFailure() && then Push1(s, k)
                                // else 
    ]   

    /** 
     * Evaluate the STOP bytecode.  This halts the machine without
     * return output data.
     */
    function method Stop(s:State): State  
        // requires !s.IsFailure()
    {
        if s.IsFailure() then 
             s.PropagateFailure()
        else 
            State.RETURNS(gas := s.ExtractGas(), data := [])  
    }

    /**
   * Unsigned integer addition with modulo arithmetic.
   */
  function method Add(s: State) : State
//   requires st.OK? 
  {
    if s.IsFailure() then 
        s.PropagateFailure()
    else if s.operands() >= 2 
      then 
        // var lhs := peek(vm,0) as int;
        // var rhs := peek(vm,1) as int;
        // var res := (lhs + rhs) % TWO_256;
    //   next(push(pop(pop(st.Extract())),res as u256))
        s
    else
      State.INVALID
  }

//   /**
//    * Unsigned integer multiplication with modulo arithmetic.
//    */
//   function method Mul(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0) as int;
//       var rhs := peek(vm,1) as int;
//       var res := (lhs * rhs) % TWO_256;
//       next(push(pop(pop(vm)),res as u256))
//     else
//       State.INVALID
//   }

//   /**
//    * Unsigned integer subtraction with modulo arithmetic.
//    */
//   function method Sub(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0) as int;
//       var rhs := peek(vm,1) as int;
//       var res := (lhs - rhs) % TWO_256;
//       next(push(pop(pop(vm)),res as u256))
//     else
//       State.INVALID
//   }

//   /**
//    * Unsigned integer division.
//    */
//   function method Div(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0);
//       var rhs := peek(vm,1);
//       var res := div(lhs,rhs) as u256;
//       next(push(pop(pop(vm)),res))
//     else
//       State.INVALID
//   }

//   /**
//    * Signed integer division.
//    */
//   function method SDiv(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := Word.asI256(peek(vm,0));
//       var rhs := Word.asI256(peek(vm,1));
//       var res := Word.fromI256(sdiv(lhs,rhs));
//       next(push(pop(pop(vm)),res))
//     else
//       State.INVALID
//   }

//   /**
//    * (Unsigned) Modulo remainder.
//    */
//   function method Mod(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0);
//       var rhs := peek(vm,1);
//       var res := mod(lhs,rhs) as u256;
//       next(push(pop(pop(vm)),res))
//     else
//       State.INVALID
//   }

//   /**
//    * Signed integer remainder:
//    */
//   function method SMod(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := Word.asI256(peek(vm,0));
//       var rhs := Word.asI256(peek(vm,1));
//       var res := Word.fromI256(smod(lhs,rhs));
//       next(push(pop(pop(vm)),res))
//     else
//       State.INVALID
//   }

//   /**
//    * Unsigned integer modulo addition.
//    */
//   function method AddMod(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 3
//       then
//       var lhs := peek(vm,0) as int;
//       var rhs := peek(vm,1) as int;
//       var rem := peek(vm,2) as int;
//       var res := if rem == 0 then 0 else(lhs + rhs) % rem;
//       next(push(pop(pop(pop(vm))),res as u256))
//     else
//       State.INVALID
//   }

//   /**
//    * Unsigned integer modulo multiplication.
//    */
//   function method MulMod(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 3
//       then
//       var lhs := peek(vm,0) as int;
//       var rhs := peek(vm,1) as int;
//       var rem := peek(vm,2) as int;
//       var res := if rem == 0 then 0 else(lhs * rhs) % rem;
//       next(push(pop(pop(pop(vm))),res as u256))
//     else
//       State.INVALID
//   }

//   /**
//    * (Unsigned) less-than comparison.
//    */
//   function method Lt(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0);
//       var rhs := peek(vm,1);
//       if lhs < rhs
//         then
//         next(push(pop(pop(vm)),1))
//       else
//         next(push(pop(pop(vm)),0))
//     else
//       State.INVALID
//   }

//   /**
//    * (Unsigned) greater-than comparison.
//    */
//   function method Gt(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0);
//       var rhs := peek(vm,1);
//       if lhs > rhs
//         then
//         next(push(pop(pop(vm)),1))
//       else
//         next(push(pop(pop(vm)),0))
//     else
//       State.INVALID
//   }

//   /**
//    * Signed less-than comparison.
//    */
//   function method SLt(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := Word.asI256(peek(vm,0));
//       var rhs := Word.asI256(peek(vm,1));
//       if lhs < rhs
//         then
//         next(push(pop(pop(vm)),1))
//       else
//         next(push(pop(pop(vm)),0))
//     else
//       State.INVALID
//   }

//   /**
//    * Signed greater-than comparison.
//    */
//   function method SGt(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := Word.asI256(peek(vm,0));
//       var rhs := Word.asI256(peek(vm,1));
//       if lhs > rhs
//         then
//         next(push(pop(pop(vm)),1))
//       else
//         next(push(pop(pop(vm)),0))
//     else
//       State.INVALID
//   }

//   /**
//    * Equality comparison.
//    */
//   function method Eq(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0);
//       var rhs := peek(vm,1);
//       if lhs == rhs
//         then
//         next(push(pop(pop(vm)),1))
//       else
//         next(push(pop(pop(vm)),0))
//     else
//       State.INVALID
//   }

//   /**
//    * Simple not operator.
//    */
//   function method IsZero(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 1
//       then
//       var mhs := peek(vm,0);
//       if mhs == 0
//         then
//         next(push(pop(vm),1))
//       else
//         next(push(pop(vm),0))
//     else
//       State.INVALID
//   }

//   /**
//    * Bitwise AND operation.
//    */
//   function method And(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0) as bv256;
//       var rhs := peek(vm,1) as bv256;
//       var res := (lhs & rhs) as u256;
//       next(push(pop(pop(vm)),res))
//     else
//       State.INVALID
//   }

//   /**
//    * Bitwise OR operation.
//    */
//   function method {:verify false} Or(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0) as bv256;
//       var rhs := peek(vm,1) as bv256;
//       var res := (lhs | rhs) as u256;
//       next(push(pop(pop(vm)),res))
//     else
//       State.INVALID
//   }

//   /**
//    * Bitwise XOR operation.
//    */
//   function method {:verify false} Xor(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0) as bv256;
//       var rhs := peek(vm,1) as bv256;
//       var res := (lhs ^ rhs) as u256;
//       next(push(pop(pop(vm)),res))
//     else
//       State.INVALID
//   }

//   /**
//    * Bitwise NOT operation.
//    */
//   function method Not(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 1
//       then
//       var mhs := peek(vm,0) as bv256;
//       var res := (!mhs) as u256;
//       next(push(pop(vm),res))
//     else
//       State.INVALID
//   }

//   /**
//    * Retrieve single byte from word.
//    */
//   function method Byte(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var val := peek(vm,1);
//       var k := peek(vm,0);
//       var res := if k < 32 then U256.nth_u8(val,k as int) else 0;
//       next(push(pop(pop(vm)),res as u256))
//     else
//       State.INVALID
//   }

//   /**
//    * Left shift operation.
//    */
//   function method Shl(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0);
//       var rhs := peek(vm,1) as bv256;
//       // NOTE: unclear whether shifting is optimal choice here.
//       var res := if lhs < 256 then (rhs << lhs) else 0;
//       next(push(pop(pop(vm)),res as u256))
//     else
//       State.INVALID
//   }

//   /**
//    * Right shift operation.
//    */
//   function method {:verify false} Shr(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var lhs := peek(vm,0);
//       var rhs := peek(vm,1) as bv256;
//       // NOTE: unclear whether shifting is optimal choice here.
//       var res := if lhs < 256 then (rhs >> lhs) else 0;
//       next(push(pop(pop(vm)),res as u256))
//     else
//       State.INVALID
//   }

//   /**
//    * Get input data from the current environment.
//    */
//   function method CallDataLoad(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 1
//       then
//       var loc := peek(vm,0);
//       var val := if loc >= Context.data_size(vm.context) then 0
//         else Context.data_read(vm.context,loc);
//       next(push(pop(vm),val))
//     else
//       State.INVALID
//   }

//   /**
//    * Get size of input data in current environment.
//    */
//   function method CallDataSize(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if capacity(vm) >= 1
//       then
//       var len := |vm.context.calldata|;
//       next(push(vm,len as u256))
//     else
//       State.INVALID
//   }

//   /**
//    * Get size of input data in current environment.
//    */
//   function method CallDataCopy(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 3
//       then
//       var m_loc := peek(vm,0);
//       var d_loc := peek(vm,1);
//       var len := peek(vm,2);
//       // NOTE: This condition is not specified in the yellow paper.
//       // Its not clear whether that was intended or not.  However, its
//       // impossible to trigger this in practice (due to the gas costs
//       // involved).
//       if (m_loc as int) + (len as int) < MAX_U256
//       then
//         // Slice bytes out of call data (with padding as needed)
//         var data := Context.data_slice(vm.context,d_loc,len);
//         // Sanity check
//         assert |data| == (len as int);
//         // Copy slice into memory
//         next(copy(pop(pop(pop(vm))),m_loc,data))
//       else
//         State.INVALID
//     else
//       State.INVALID
//   }

  /**
   * Pop word from stack.
   */
  function method Pop(s: State) : State
  {
    if s.IsFailure() then 
        s.PropagateFailure()
    else if s.operands() >= 1 then
        next(pop(s.Extract()))
    else
      State.INVALID
  }

//   /**
//    * Get word from memory.
//    */
//   function method MLoad(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 1
//       then
//       var loc := peek(vm,0);
//       // NOTE: This condition is not specified in the yellow paper.
//       // Its not clear whether that was intended or not.  However, its
//       // impossible to trigger this in practice (due to the gas costs
//       // involved).
//       if (loc as int) + 31 <= MAX_U256
//         then
//         var val := read(vm,loc);
//         // Write big endian order
//         next(push(pop(vm),val))
//       else
//         State.INVALID
//     else
//       State.INVALID
//   }


//   /**
//    * Save word to memory.
//    */
//   function method MStore(st: State) : State
//   requires st.OK? {

//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var loc := peek(vm,0);
//       var val := peek(vm,1);
//       // NOTE: This condition is not specified in the yellow paper.
//       // Its not clear whether that was intended or not.  However, its
//       // impossible to trigger this in practice (due to the gas costs
//       // involved).
//       if (loc as int) + 31 <= MAX_U256
//         then
//         // Write big endian order
//         next(write(pop(pop(vm)),loc,val))
//       else
//         State.INVALID
//     else
//       State.INVALID
//   }

//   /**
//    * Save byte to memory.
//    */
//   function method MStore8(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var loc := peek(vm,0);
//       var val := (peek(vm,1) % 256) as u8;
//       if (loc as int) < MAX_U256
//         then
//         // Write byte
//         next(write8(pop(pop(vm)),loc,val))
//       else
//         State.INVALID
//     else
//       State.INVALID
//   }

//   /**
//    * Get word from storage.
//    */
//   function method SLoad(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 1
//       then
//       var loc := peek(vm,0);
//       var val := load(vm,loc);
//       // Store word
//       next(push(pop(vm),val))
//     else
//       State.INVALID
//   }

//   /**
//    * Save word to storage.
//    */
//   function method SStore(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var loc := peek(vm,0);
//       var val := peek(vm,1);
//       // Store word
//       next(store(pop(pop(vm)),loc,val))
//     else
//       State.INVALID
//   }

//   /**
//    * Unconditional branch.
//    */
//   function method Jump(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 1
//       then
//       var pc := peek(vm,0);
//       // Check valid branch target
//       if pc < Code.size(vm.code) && Code.decode_u8(vm.code,pc as nat) == JUMPDEST
//       then
//         goto(pop(vm),pc)
//       else
//         State.INVALID
//     else
//       State.INVALID
//   }

//   /**
//    * Unconditional branch.
//    */
//   function method JumpI(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       var pc := peek(vm,0);
//       var val := peek(vm,1);
//       // Check branch taken or not
//       if val == 0 then next(pop(pop(vm)))
//       // Check valid branch target
//       else if pc < Code.size(vm.code) && Code.decode_u8(vm.code,pc as nat) == JUMPDEST
//       then
//         goto(pop(pop(vm)),pc)
//       else
//         State.INVALID
//     else
//       State.INVALID
//   }

//   /**
//    * Gets value of program counter prior to this instruction being executed.
//    */
//   function method Pc(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if capacity(vm) >= 1
//     then
//       next(push(vm, vm.pc))
//     else
//       State.INVALID
//   }

//   /**
//    * Marks a valid destination for a jump, but otherwise has no effect
//    * on machine state.
//    */
//   function method JumpDest(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st; next(vm)
//   }

  /**
   * Push one byte onto stack.
   */
  function method Push1(s: State, k: u8) : State 
  {
    if s.IsFailure() then 
        s.PropagateFailure()
    else if Stack.capacity(s.Extract().stack) >= 1 then
        skip(push(s.Extract(), k as u256),2)
    else
        State.INVALID
  }

//   /**
//    * Push two bytes onto stack.
//    */
//   function method Push2(st: State, k: u16) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if capacity(vm) >= 1
//       then
//       skip(push(vm,k as u256),3)
//     else
//       State.INVALID
//   }

//   /**
//    * Duplicate item on stack.
//    */
//   function method Dup(st: State, k: nat) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) > k && capacity(vm) >= 1
//       then
//       var kth := peek(vm,k);
//       next(push(vm,kth))
//     else
//       State.INVALID
//   }

//   /**
//    * Swap two items on the stack
//    */
//   function method Swap(st: State, k: nat) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) > k
//       then
//       next(swap(vm,k))
//     else
//       State.INVALID
//   }

//   /**
//    * Halt execution returning output data.
//    */
//   function method Return(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       // Determine amount of data to return.
//       var len := peek(vm,1) as int;
//       var start := peek(vm,0) as int;
//       // Sanity check bounds
//       if (start+len) <= MAX_U256
//       then
//         // Read out that data.
//         var data := Memory.slice(vm.memory, start as u256, len);
//         // Done
//         State.RETURNS(gas:=vm.gas,data:=data)
//       else
//         State.INVALID
//     else
//       State.INVALID
//   }

//   /**
//    * Revert execution returning output data.
//    */
//   function method Revert(st: State) : State
//   requires st.OK? {
//     var OK(vm) := st;
//     //
//     if operands(vm) >= 2
//       then
//       // Determine amount of data to return.
//       var len := peek(vm,1) as int;
//       var start := peek(vm,0) as int;
//       // Sanity check bounds
//       if (start+len) <= MAX_U256
//       then
//         // Read out that data.
//         var data := Memory.slice(vm.memory, start as u256, len);
//         // Done
//         State.REVERT(gas:=vm.gas,data:=data)
//       else
//         State.INVALID
//     else
//       State.INVALID
//   }


}

import opened EVM_OPCODES  
import opened E = EVM_BERLIN  
import opened Int

// Check most simple program possible
method test_01(x: u8)
requires x > 1
{
  // Initialise EVM
  var tx := Context.create(0xabcd,[]);
  var vm := E.create(tx,map[],100,
    // [PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]
    [STOP]
    );
  // PUSH1 x
  vm := E.execute(vm);
  // PUSH1 0x2
  assert vm.RETURNS?;
//   vm := E.execute(vm);
//   // MSTORE
//   vm := E.execute(vm);
//   // PUSH
//   vm := E.execute(vm);
//   // PUSH
//   vm := E.execute(vm);
//   // RETURN
//   var r := E.execute(vm);
  //
//   assert data(r) == [x];
}

