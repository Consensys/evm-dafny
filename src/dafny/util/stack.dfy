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

    // Maximum stack capcity is 1024 words.
    const CAPACITY : int := 1024;

    // A raw stack consistents of a sequence of data, and a stack pointer.
    datatype Raw = Stack(contents:seq<u256>)

    // A valid Stack cannot exceed the capacity.
    type T = s:Raw | |s.contents| <= CAPACITY
    witness Stack([])

    // Get number of items currently on this Stack.
    function method size(st:T) : nat { |st.contents| }

    // Get remaining capacity of stack (i.e. number of items we could
    // still push).
    function method capacity(st:T) : nat {
      CAPACITY - |st.contents|
    }

    // Create an empty stack.
    function method create() : T { Stack(contents:=[]) }

    // Push word onto Stack.  This requires that there is sufficient
    // space for that item.
    function method push(st:T, val:u256) : T
        // Sanity check enough space.
        requires size(st) < CAPACITY {
            Stack(contents:=([val] + st.contents))
    }

    // Peek nth word from top of Stack (where 0 is top item, 1 is next
    // item, and so on).  This requires there are sufficiently many
    // words.
    function method peek(st:T, k:int) : u256
        // Sanity check enough items to pop!
        requires k >= 0 && k < size(st) {
            st.contents[k]
    }

    // Pop word off of this Stack.  This requires something to pop!
    function method pop(st:T) : T
        // Sanity check something to pop.
        requires size(st) > 0 {
            Stack(contents:=st.contents[1..])
    }

    // Swap top item and kth item
    function method swap(st:T, k:nat) : T
      requires size(st) > k {
        var top := st.contents[0];
        var kth := st.contents[k];
        Stack(contents:=st.contents[0:=kth][k:=top])
    }
}
