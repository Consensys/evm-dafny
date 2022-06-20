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
include "int.dfy"

module Stack {
    import opened Int

    /**
     * Maximum stack capcity is 1024 words.
     */
    const CAPACITY : int := 1024;

    /**
     * A raw stack consistents of a sequence of data, and a stack pointer.
     */
    datatype Raw = Stack(contents:seq<uint256>, sp:nat)

    /**
     * A valid Stack: (1) must have a stack pointer within bounds;
     * (2) cannot have more than 1024 items.  Note, the stack
     * pointer identifies the first *unused* slot on the stack.
     */
    type T = s:Raw | s.sp <= |s.contents| && |s.contents| <= CAPACITY
    witness Stack([],0)

    /**
     * Get number of items currently on this Stack.
     */
    function size(st:T) : int { st.sp }

    /**
     * Create an empty stack.
     */
    function method create() : T { Stack(contents:=[],sp:=0) }

    /**
     * Push word onto Stack.  This requires that there is sufficient
     * space for that item.
     */
    function push(st:T, val:uint256) : T
        // Sanity check enough space.
        requires size(st) < |st.contents| {
            Stack(contents:=st.contents[st.sp:=val],sp:=st.sp+1)
    }

    /**
     * Peek nth word from top of Stack (where 1 is top item, 2 is next item,
     * and so on).  This requires there are sufficiently many words.
     */
    function peek(st:T, k:int) : uint256
        // Sanity check enough items to pop!
        requires k > 0 && k <= size(st) {
            st.contents[st.sp-k]
    }

    /**
     * Pop word off of this Stack.  This requires something to pop!
     */
    function pop<S>(st:T) : T
        // Sanity check something to pop.
        requires size(st) > 0 {
            Stack(contents:=st.contents,sp:=st.sp-1)
    }
}
