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

    datatype T = Memory(contents:map<u256,u8>)

    /**
     * Create a memory from an initial sequence of words.
     */
    function method create() : T {
        Memory(contents:=map[])
    }

    /**
     * Read the byte at a given address in Memory.  If the given location
     * has not been initialised, then zero is returned as default.
     */
    function method read_u8(mem:T, address:u256) : u8 {
        // Read location
        if address in mem.contents
        then
          mem.contents[address]
        else
          0
    }

    /**
     * Write a byte to a given address in Memory.
     */
    function method write_u8(mem:T, address:u256, val:u8) : T {
        // Write location
        Memory(contents:=mem.contents[address:=val])
    }

    /**
     * Write a 16bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method write_u16(mem:T, address:u256, val:u16) : T
    requires (address as int) + 1 <= MAX_UINT256 {
      var b1 := val / (TWO_8 as u16);
      var b2 := val % (TWO_8 as u16);
      var mem' := write_u8(mem,address,b1 as u8);
      write_u8(mem,address+1,b2 as u8)
    }

    /**
     * Write a 32bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method write_u32(mem:T, address:u256, val:u32) : T
    requires (address as int) + 3 <= MAX_UINT256 {
      var b1 := val / (TWO_16 as u32);
      var b2 := val % (TWO_16 as u32);
      var mem' := write_u16(mem,address,b1 as u16);
      write_u16(mem,address+2,b2 as u16)
    }

    /**
     * Write a 64bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method write_u64(mem:T, address:u256, val:u64) : T
    requires (address as int) + 7 <= MAX_UINT256 {
      var b1 := val / (TWO_32 as u64);
      var b2 := val % (TWO_32 as u64);
      var mem' := write_u32(mem,address,b1 as u32);
      write_u32(mem,address+4,b2 as u32)
    }

    /**
     * Write a 128bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method write_u128(mem:T, address:u256, val:u128) : T
    requires (address as int) + 15 <= MAX_UINT256 {
      var b1 := val / (TWO_64 as u128);
      var b2 := val % (TWO_64 as u128);
      var mem' := write_u64(mem,address,b1 as u64);
      write_u64(mem,address+8,b2 as u64)
    }

    /**
     * Write a 256bit word to a given address in Memory using
     * big-endian addressing.
     */
    function method write_u256(mem:T, address:u256, val:u256) : T
    requires (address as int) + 31 <= MAX_UINT256 {
      var b1 := val / (TWO_128 as u256);
      var b2 := val % (TWO_128 as u256);
      var mem' := write_u128(mem,address,b1 as u128);
      write_u128(mem,address+16,b2 as u128)
    }

    /**
     * Slice out a section of memory.
     */
    function method slice(mem:T, address:u256, len:nat) : seq<u8>
      requires (address as int + len) <= MAX_UINT256
      decreases len
    {
      if len == 0 then
        []
      else if address in mem.contents
        then
        [mem.contents[address]] + slice(mem,address+1,len-1)
      else
        [0] + slice(mem,address+1,len-1)
    }
}
