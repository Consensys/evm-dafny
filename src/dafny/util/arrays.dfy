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

module Arrays {
    import opened Int
    /**
     * A fixed size array which is bounded by the maximum word size.  Thus, it
     * represents an array (e.g. of bytes) which could appear as part of the EVM
     * state (e.g. CALLDATA or RETURDATA).  Thus, the length of the array can be
     * reasonably turned into a u256 and (for example) loaded on the stack.
     */
    type Array<T> = arr:seq<T> | |arr| < TWO_256

    /**
     * Everything is the same, except for those elements within the given region.
     */
    predicate EqualsExcept<T(==)>(lhs:seq<T>, rhs:seq<T>, address:nat, length: nat)
    // Data region must be within available memory
    requires address + length <= |lhs| {
        // Memory sizes are the same
        |lhs| == |rhs| &&
        // Check nothing below data region changed
        lhs[..address] == rhs[..address] &&
        // Check nothing above data region changed
        lhs[address+length..] == rhs[address+length..]
    }

    /**
     * Copy a sequence of bytes from into another at a given starting position.
     */
    opaque function Copy<T>(src: seq<T>, dst: seq<T>, start: nat) : (result:seq<T>)
    // Must have enough space in the destination sequence.
    requires (start+|src|) <= |dst|
    // Resulting array unchanged in size
    ensures |result| == |dst|
    // Affected region matches source array
    ensures src == result[start .. (start+|src|)]
    // Everything unchanged outside affected region
    ensures EqualsExcept(dst,result,start,|src|)
    {
        // Precompute end within destination
        var end := start+|src|;
        // Construct the sequence!
        seq(|dst|, i requires i >= 0 && i < |dst| => if (i >= start && i<end) then src[i-start] else dst[i])
    }
}
