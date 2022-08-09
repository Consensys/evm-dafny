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
include "bytes.dfy"

/**
 * Memory on the EVM is a byte-addressable (volatile) random access memory.
 */
module Memory {
    import opened Int
    import U256
    import opened Bytes

    // =============================================================================
    // Random Access Memory
    // =============================================================================

    datatype T = Memory(contents:seq<u8>)

    /**
     * Create a memory from an initial sequence of words.
     */
    function method Create() : T {
        Memory(contents:=[])
    }

    /**
     * Return size of memory (in bytes).
     */
    function method Size(mem:T) : nat { |mem.contents| }

    function method
        ceiling(n: nat, m: nat): (o: nat)
        requires m > 0
        ensures n / m <= o <= n / m + 1
            {
                if n % m == 0
                    then n / m
                else 
                    (n / m) + 1
            }

    /* this is the function M (YP, page 29, BERLIN VERSION 3078285 – 2022-07-13) */
    function method
        maxMemoryUsedSizeExpansion(s: nat, f: nat, l: nat): nat
            {
                if  l == 0
                    then s
                else
                    Int.Max(s, ceiling(f + l, 32))
            }
            
    /**
     *  Expand memory if needed.
     *
     *  @param  mem     The memory representation.
     *  @param  address The start address to read from.
     *  @param  len     The number of bytes to read.
     *  @returns        
     *
     *  @note           The memory size is a multiple of 32.
     *  @example        `mem` is `[20, 21, 22, 23]
     *                  `Expand(mem, k, 1)` for `0 <= k < 4` is `mem`.
     *                  `Expand(mem, 2, 2)` expands memory as the elem
     */
    function method Expand(mem:T, address: nat, len: nat) : (r:T) 
      ensures |r.contents| >= address + len 
      // ensures address + len > |mem.contents| ==> |r.contents| % 32 == 0 
    {
          if address + len <= |mem.contents|
            then mem
          else
            var expansionAmount := ceiling(address + len + 1 - |mem.contents|, 32) * 32;
            mem.(contents := mem.contents + Padding(expansionAmount))
    }

    /**
     *  Expand memory if needed.
     *
     *  @param  mem     The memory representation.
     *  @param  address The largest address to read from.
     *  @returns        
     *
     *  @note           The memory size is a multiple of 32.
     *  @example        `mem` is `[20, 21, 22, 23].
     *                  ExpandRec(mem, k)` for `0 <= k < 4` is mem.
     *                  If `k >= 4`, then `mem` is expanded by 32 bytes until
     *                  `address < |mem.contents|`. 
     */
    function method {:tailrecursion} Expand2(mem:T, address: nat) : (r:T) 
      ensures |r.contents| > address
      decreases address - |mem.contents|
    {
          if address < |mem.contents|
            then mem
          else
            Expand2(mem.(contents := mem.contents + Padding(32)), address)
    }

    /* implements the function M in (YP, page 29, BERLIN VERSION 3078285 – 2022-07-13), and expands the memory if needed */
    // function method Expand_CompleteVersion(mem:T, address: nat, length: nat) : T {
    //   if length == 0
    //     then mem
    //   else
    //     var checkForExpanansion := maxMemoryUsedSizeExpansion(|mem.contents|, address, length);
    //     if checkForExpanansion == |mem.contents|
    //       then mem
    //     else 
    //       var expansionAmount := (checkForExpanansion - |mem.contents|) * 32;
    //       mem.(contents := mem.contents + Padding(expansionAmount))
     
    //   // Round up size to multiple of 32.
    //  // var rounded := RoundUp((address as nat)+1,32);
    //  // mem.(size:=Max(mem.size,rounded))
    // }

    /**
     * Read the byte at a given address in Memory.  If the given location
     * has not been initialised, then zero is returned as default.
     */
    function method ReadUint8(mem:T, address:nat) : u8 {
        // Read location
        if address < |mem.contents|
        then
          mem.contents[address]
        else
          0
    }

    /**
     * Read a 16bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint16(mem:T, address:nat) : u16
      requires address + 1 < |mem.contents| {
        var w1 := ReadUint8(mem,address) as u16;
        var w2 := ReadUint8(mem,address+1) as u16;
        (w1 * (TWO_8 as u16)) + w2
    }

    /**
     * Read a 32bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint32(mem:T, address:nat) : u32
      requires address + 3 < |mem.contents| {
        var w1 := ReadUint16(mem,address) as u32;
        var w2 := ReadUint16(mem,address+2) as u32;
        (w1 * (TWO_16 as u32)) + w2
    }

    /**
     * Read a 64bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint64(mem:T, address:nat) : u64
      requires address + 7 < |mem.contents| {
        var w1 := ReadUint32(mem,address) as u64;
        var w2 := ReadUint32(mem,address+4) as u64;
        (w1 * (TWO_32 as u64)) + w2
    }

    /**
     * Read a 128bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint128(mem:T, address:nat) : u128
      requires address + 15 < |mem.contents| {
        var w1 := ReadUint64(mem,address) as u128;
        var w2 := ReadUint64(mem,address+8) as u128;
        (w1 * (TWO_64 as u128)) + w2
    }

    /**
     * Read a 256bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint256(mem:T, address:nat) : u256
      requires address + 31 < |mem.contents| {
        var w1 := ReadUint128(mem,address) as u256;
        var w2 := ReadUint128(mem,address+16) as u256;
        (w1 * (TWO_128 as u256)) + w2
    }

    /**
     * Write a byte to a given address in Memory.
     */

    function method WriteUint8(mem:T, address:nat, val:u8) : T
        requires address < |mem.contents| {
        // Update size calc.
        // Write location
        Memory(contents:=mem.contents[address:=val])
    }

    /**
     * Write a 16bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint16(mem:T, address:nat, val:u16) : T
    requires address + 1 < |mem.contents| {
      var w1 := val / (TWO_8 as u16);
      var w2 := val % (TWO_8 as u16);
      var mem' := WriteUint8(mem,address,w1 as u8);
      WriteUint8(mem',address+1,w2 as u8)
    }

    /**
     * Write a 32bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint32(mem:T, address:nat, val:u32) : T
    requires address + 3 < |mem.contents| {
      var w1 := val / (TWO_16 as u32);
      var w2 := val % (TWO_16 as u32);
      var mem' := WriteUint16(mem,address,w1 as u16);
      WriteUint16(mem',address+2,w2 as u16)
    }

    /**
     * Write a 64bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint64(mem:T, address:nat, val:u64) : T
    requires address + 7 < |mem.contents| {
      var w1 := val / (TWO_32 as u64);
      var w2 := val % (TWO_32 as u64);
      var mem' := WriteUint32(mem,address,w1 as u32);
      WriteUint32(mem',address+4,w2 as u32)
    }

    /**
     * Write a 128bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint128(mem:T, address:nat, val:u128) : T
    requires address + 15 < |mem.contents| {
      var w1 := val / (TWO_64 as u128);
      var w2 := val % (TWO_64 as u128);
      var mem' := WriteUint64(mem,address,w1 as u64);
      WriteUint64(mem',address+8,w2 as u64)
    }

    /**
     * Write a 256bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint256(mem:T, address:nat, val:u256) : T
    requires address + 31 < |mem.contents| {
      var w1 := val / (TWO_128 as u256);
      var w2 := val % (TWO_128 as u256);
      var mem' := WriteUint128(mem,address,w1 as u128);
      WriteUint128(mem',address+16,w2 as u128)
    }

    /** Extract a subsequence of memory.
     *  
     *  @param  mem     The memory representation.
     *  @param  address The start of the slice.
     *  @param  len     The number of bytes to extract.
     *  @return         `len` bytes starting at `address`.
     *
     *  @example        mem is [10, 11, 13]
     *                  SliceRec(mem, 4, 0) == []       // len is 0
     *                  SliceRec(mem, 2, 1) == [13]     // start at index 2, 1 elements
     *                  SliceRec(mem, 0, 2) == [10, 11] // start at index 0, 2 elements
     *  @note           The first element read is at `address` and the last one at `address + len - 1`
     *                  so the constraint should `(address + len) <= |mem.contents|`.
     */
    function method {:tailrec} Slice(mem:T, address:nat, len:nat) : seq<u8>
      requires (address + len) <= |mem.contents| 
      ensures |Slice(mem, address, len)| == len 
      decreases len
    {
      if len == 0 then
        []
      else 
        [ReadUint8(mem,address)] + Slice(mem, address + 1, len - 1)
    }

    function method Copy(mem:T, address:nat, data:seq<u8>) : T
      requires (address + |data|) <= |mem.contents|
      decreases |data| {
        if |data| == 0 then mem
        else
          var step := WriteUint8(mem,address,data[0]);
          Copy(step,address+1,data[1..])
    }
}
