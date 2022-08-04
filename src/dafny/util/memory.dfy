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

/**
 * Memory on the EVM is a byte-addressable (volatile) random access memory.
 */
module Memory {
    import opened Int

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

    /**
     * Slice out a section of memory.  This is implemented in a subdivision
     * style as this seems to work better (in terms of theorem prover performance).
     */
    function method Slice(mem:T, address:nat, len:nat) : seq<u8>
      requires (address + len) < |mem.contents| 
      decreases len
    {
      if len == 0
      then
        []
      else if len == 1
        then
        [ReadUint8(mem,address)]
      else
        var pivot := len / 2;
        var middle := address + pivot;
        Slice(mem,address,pivot) + Slice(mem,middle, len - pivot)
    }

    function method Copy(mem:T, address:nat, data:seq<u8>) : T
      requires (address + |data|) < |mem.contents|
      decreases |data| {
        if |data| == 0 then mem
        else
          var step := WriteUint8(mem,address,data[0]);
          Copy(step,address+1,data[1..])
    }

    /* the following does not get fixed easily. I am commenting it out but am keeping it for later, if useful. Note that a linear time implementation does just fine and is more 
        verification friendly */
    /**
     * Copy a sequence of bytes into this memory at a given address. 
     
    function method Copy2(mem:T, address:nat, data:seq<u8>) : T
      requires (address + |data|) < |mem.contents|
      decreases |data| {
        if |data| == 0 then mem
        else if |data| == 1 then WriteUint8(mem,address,data[0])
        else
          var pivot := |data| / 2;
          var middle := address + pivot;
          var nmem := Copy2(mem,address,data[0..pivot]);
          Copy2(nmem,middle,data[pivot..])
    }
    */
}
