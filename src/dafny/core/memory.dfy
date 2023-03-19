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
include "../util/arrays.dfy"
include "../util/bytes.dfy"
include "../util/int.dfy"

/**
 * Memory on the EVM is a byte-addressable (volatile) random access memory.
 */
module Memory {
    import opened Int
    import U256
    import Arrays
    import opened Bytes

    // =============================================================================
    // Random Access Memory
    // =============================================================================

    datatype T = Memory(contents:seq<u8>)

    /**
     * Create a memory from an initial sequence of words.
     */
    function Create() : T {
        Memory(contents:=[])
    }

    /**
     * Return size of memory (in bytes).
     */
    function Size(mem:T) : nat { |mem.contents| }

    /** Expand memory size if needed.
     *
     *  @param  mem     A memory representation.
     *  @param  address An address to read (an u8) in memory.
     *  @returns        The smallest extension of `mem` that contains `address`
     *                  and has a multiple of 32 bytes elements.
     *
     *  @note           At the end, `address` should be a valid index of `r`
     *                  i.e. in 0..(r.size - 1).
     */
    function Expand(mem: T, address: nat) : (r: T)
      ensures |r.contents| > address
      ensures address >= |mem.contents| ==>
        (|r.contents| % 32 == 0 &&  |r.contents| - 32 <= address)
    {
        if address < |mem.contents| then
          mem
        else
          var extLength := SmallestLarg32(address);
          mem.(contents := mem.contents + Padding(extLength - |mem.contents|))
    }

    /** Smallest number multiple of 32 that is larger than k. */
    function SmallestLarg32(k: nat): (x:nat)
      ensures x > k
      ensures x % 32 == 0
      ensures (x - 32) <= k
    {
      (k / 32 + 1) * 32
    }

    /**
     *  Expand memory to include a given address.
     *  Calls the function Expand2 implemented in the memory module

     *  @param  address The start address.
     *  @param  len     The number of bytes to read from `address`, i.e.
     *                  we want to read `len` bytes starting at `address`.
     *  @returns        A possibly expanded memory that contains
     *                  memory slots upto index `address + len - 1`.
     *
     *  @note           When using this function, you may check
     *                  first that the extended chunk satisfies some constraints,
     *                  e.g. begin less then `MAX_U256`.
     */
    function ExpandMem(mem: T, address: nat, len: nat): (r: T)
    requires len > 0
    {
        Expand(mem, address + len - 1)
    }

    // =============================================================================
    //  Read/Write helpers
    // =============================================================================

    /**
     * Read a 256bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function ReadUint256(mem:T, address:nat) : u256
      requires address + 31 < |mem.contents| {
       Bytes.ReadUint256(mem.contents,address)
    }

    /**
     * Write a byte to a given address in Memory.
     */
    function WriteUint8(mem:T, address:nat, val:u8) : T
    requires address < |mem.contents| {
        // Write location
        Memory(contents:=mem.contents[address:=val])
    }

    /**
     * Write a 256bit word to a given address in Memory using
     * big-endian addressing.
     */
    function WriteUint256(mem:T, address:nat, val:u256) : (mem':T)
    requires address + 31 < |mem.contents|
    // Nothing has changed except the bytes overwritten by the u256
    ensures Arrays.EqualsExcept(mem.contents,mem'.contents,address,32) {
        var ncontents := Bytes.WriteUint256(mem.contents,address,val);
        Memory(contents:=ncontents)
    }

    /**
     * Slice out a section of memory.
     */
    function Slice(mem:T, address:nat, len:nat) : (result:seq<u8>)
    ensures |result| == len
    {
      Arrays.SliceAndPad(mem.contents,address,len,0)
    }

    /**
     * Copy a sequence of bytes into this memory at a given address.  This uses
     * a decomposition technique (rather than the obvious iterative technique)
     * as the former seems to improve verification performance.
     */
    function Copy(mem:T, address:nat, data:seq<u8>) : (mem':T)
    // Must have sufficient memory for copy.
    requires |data| == 0 || (address + |data|) <= |mem.contents|
    {
        if |data| == 0 then mem
        else
            Memory(Arrays.Copy(data,mem.contents,address))
    }
}
