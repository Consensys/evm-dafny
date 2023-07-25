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
include "../util/int.dfy"

/** Provide a Stack and related operations. */
module Stack {
    import opened Int

    // Maximum stack capcity is 1024 words.
    const CAPACITY: nat := 1024

    /** The stack has limited capcity in the EVM. */
    type ValidStackContent = xs: seq<u256> | |xs| <= CAPACITY

    /** The Stack type. */
    datatype EvmStack = Stack(contents: ValidStackContent)
    {
        // Get number of items currently on this Stack.
        function Size(): nat { |contents| }

        // Get remaining capacity of stack (i.e. number of items we could still
        // push).
        function Capacity(): nat {
            CAPACITY - |contents|
        }

        // Push word onto Stack.  This requires that there is sufficient space for
        // that item.
        function Push(val: u256): EvmStack
            // Sanity check enough space.
            requires this.Size() < CAPACITY {
                Stack(contents:=([val] + contents))
        }

        // Peek nth word from top of Stack (where 0 is top item, 1 is next item, and
        // so on).  This requires there are sufficiently many words.
        function Peek(k: nat) : u256
            // Sanity check enough items to pop!
            requires k >= 0 && k < this.Size() {
                contents[k]
        }

        // Peek top N words on the Stack.  This requires there are sufficiently many
        // words.
        function PeekN(n: nat) : (r:seq<u256>)
        requires this.Size() >= n
        ensures |r| == n {
                contents[..n]
        }

        // Pop word off of this Stack.  This requires something to pop!
        function Pop(): EvmStack
            // Sanity check something to pop.
            requires this.Size() > 0 {
                Stack(contents:= contents[1..])
        }

        // Pop N words off of this Stack.  This requires something to pop!
        function PopN(n: nat): EvmStack
            // Sanity check something to pop.
            requires this.Size() >= n {
                Stack(contents:= contents[n..])
        }

        /** Swap top item at index 0 and the k+1-th item at index k. */
        function Swap(k: nat) : EvmStack
        requires this.Size() > k > 0
        {
            var top := contents[0];
            var kth := contents[k];
            Stack(contents := contents[0:=kth][k:=top])
        }

        /**
         *  A sliced stack.
         *  @param  l   An index.
         *  @param  u   An index.
         *  @returns    The stack made of the first u elements minus the first l.
         */
        function Slice(l: nat, u: nat): (r: EvmStack)
        requires l <= u <= this.Size()
        {
            Stack(contents[l..u])
        }
    }

    //  The empty stack.
    const Empty := Stack(contents := [])

    /** Build a stack with some content. */
    function Make(xs: seq<u256>): EvmStack
        requires |xs| <= CAPACITY {
            Stack(contents := xs)
    }

    // An empty evm stack
    const EmptyEvmStack : EvmStack := Stack([])
}
