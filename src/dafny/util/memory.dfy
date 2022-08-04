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
    import U256

    // =============================================================================
    // Random Access Memory
    // =============================================================================

    datatype T = Memory(contents:map<u256,u8>,size:nat)

    /**
     * Create a memory from an initial sequence of words.
     */
    function method Create() : T {
        Memory(contents:=map[],size:=0)
    }

    /**
     * Return size of memory (in bytes).
     */
    function method Size(mem:T) : nat { mem.size }

    /**
     * Expand memory to include the given address.  Note that the EVM dictates that
     * expansion happens in multiples of 32bytes.
     */
    function method Expand(mem:T, address: u256) : T {
      // Round up size to multiple of 32.
      var rounded := RoundUp((address as nat)+1,32);
      mem.(size:=Max(mem.size,rounded))
    }

    /**
     * Read the byte at a given address in Memory.  If the given location
     * has not been initialised, then zero is returned as default.
     */
    function method ReadUint8(mem:T, address:u256) : u8 {
        // Read location
        if address in mem.contents
        then
          mem.contents[address]
        else
          0
    }

    /**
     * Read a 16bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint16(mem:T, address:u256) : u16
      requires (address as int) + 1 <= MAX_U256 {
        var w1 := ReadUint8(mem,address) as u16;
        var w2 := ReadUint8(mem,address+1) as u16;
        (w1 * (TWO_8 as u16)) + w2
    }

    /**
     * Read a 32bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint32(mem:T, address:u256) : u32
      requires (address as int) + 3 <= MAX_U256 {
        var w1 := ReadUint16(mem,address) as u32;
        var w2 := ReadUint16(mem,address+2) as u32;
        (w1 * (TWO_16 as u32)) + w2
    }

    /**
     * Read a 64bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint64(mem:T, address:u256) : u64
      requires (address as int) + 7 <= MAX_U256 {
        var w1 := ReadUint32(mem,address) as u64;
        var w2 := ReadUint32(mem,address+4) as u64;
        (w1 * (TWO_32 as u64)) + w2
    }

    /**
     * Read a 128bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint128(mem:T, address:u256) : u128
      requires (address as int) + 15 <= MAX_U256 {
        var w1 := ReadUint64(mem,address) as u128;
        var w2 := ReadUint64(mem,address+8) as u128;
        (w1 * (TWO_64 as u128)) + w2
    }

    /**
     * Read a 256bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function method ReadUint256(mem:T, address:u256) : u256
      requires (address as int) + 31 <= MAX_U256 {
        var w1 := ReadUint128(mem,address) as u256;
        var w2 := ReadUint128(mem,address+16) as u256;
        (w1 * (TWO_128 as u256)) + w2
    }

    /**
     * Write a byte to a given address in Memory.
     */
    function method WriteUint8(mem:T, address:u256, val:u8) : T {
        // Update size calc.
        var nsize := Max(mem.size, (address as nat) + 1);
        // Write location
        Memory(contents:=mem.contents[address:=val],size:=nsize)
    }

    /**
     * Write a 16bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint16(mem:T, address:u256, val:u16) : T
    requires (address as int) + 1 <= MAX_U256 {
      var w1 := val / (TWO_8 as u16);
      var w2 := val % (TWO_8 as u16);
      var mem' := WriteUint8(mem,address,w1 as u8);
      WriteUint8(mem',address+1,w2 as u8)
    }

    /**
     * Write a 32bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint32(mem:T, address:u256, val:u32) : T
    requires (address as int) + 3 <= MAX_U256 {
      var w1 := val / (TWO_16 as u32);
      var w2 := val % (TWO_16 as u32);
      var mem' := WriteUint16(mem,address,w1 as u16);
      WriteUint16(mem',address+2,w2 as u16)
    }

    /**
     * Write a 64bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint64(mem:T, address:u256, val:u64) : T
    requires (address as int) + 7 <= MAX_U256 {
      var w1 := val / (TWO_32 as u64);
      var w2 := val % (TWO_32 as u64);
      var mem' := WriteUint32(mem,address,w1 as u32);
      WriteUint32(mem',address+4,w2 as u32)
    }

    /**
     * Write a 128bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint128(mem:T, address:u256, val:u128) : T
    requires (address as int) + 15 <= MAX_U256 {
      var w1 := val / (TWO_64 as u128);
      var w2 := val % (TWO_64 as u128);
      var mem' := WriteUint64(mem,address,w1 as u64);
      WriteUint64(mem',address+8,w2 as u64)
    }

    /**
     * Write a 256bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method WriteUint256(mem:T, address:u256, val:u256) : T
    requires (address as int) + 31 <= MAX_U256 {
      var w1 := val / (TWO_128 as u256);
      var w2 := val % (TWO_128 as u256);
      var mem' := WriteUint128(mem,address,w1 as u128);
      WriteUint128(mem',address+16,w2 as u128)
    }

    /**
     * Slice out a section of memory.  This is implemented in a subdivision
     * style as this seems to work better (in terms of theorem prover performance).
     */
    function method Slice(mem:T, address:u256, len:nat) : seq<u8>
      requires (address as int + len) <= MAX_U256
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
        var middle := address + (pivot as u256);
        Slice(mem,address,pivot) + Slice(mem,middle, len - pivot)
    }

    /**
     * Copy a sequence of bytes into this memory at a given address.
     */
    function method Copy(mem:T, address:u256, data:seq<u8>) : T
      requires (address as int + |data|) <= MAX_U256
      decreases |data| {
        if |data| == 0 then mem
        else if |data| == 1 then WriteUint8(mem,address,data[0])
        else
          var pivot := |data| / 2;
          var middle := address + (pivot as u256);
          var nmem := Copy(mem,address,data[0..pivot]);
          Copy(nmem,middle,data[pivot..])
    }
}
