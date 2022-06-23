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

    function method write_bv16(mem:T, address:u256, val:bv16) : T
    // Cannot write passed end of memory.
    requires (address as int) + 1 <= MAX_UINT256 {
      var lb := (val & 0xFF) as u8;
      var hb := (val >> 8) as u8;
      Memory(contents:=mem.contents[address:=hb][address+1:=lb])
    }

    function method write_bv32(mem:T, address:u256, val:bv32) : T
    // Cannot write passed end of memory.
    requires (address as int) + 3 <= MAX_UINT256 {
      var mem' := write_bv16(mem,address,(val >> 16) as bv16);
      write_bv16(mem',address+2,(val & 0xFFFF) as bv16)
    }

    function method write_bv64(mem:T, address:u256, val:bv64) : T
    // Cannot write passed end of memory.
    requires (address as int) + 7 <= MAX_UINT256 {
      var mem' := write_bv32(mem,address,(val >> 32) as bv32);
      write_bv32(mem',address+4,(val & 0xFFFF_FFFF) as bv32)
    }

    function method write_bv128(mem:T, address:u256, val:bv128) : T
    // Cannot write passed end of memory.
    requires (address as int) + 15 <= MAX_UINT256 {
      var mem' :=write_bv64(mem,address,(val >> 64) as bv64);
      write_bv64(mem',address+8,(val & 0xFFFF_FFFF_FFFF_FFFF) as bv64)
    }

    function method write_bv256(mem:T, address:u256, val:bv256) : T
    // Cannot write passed end of memory.
    requires (address as int) + 31 <= MAX_UINT256 {
      var mem' := write_bv128(mem,address,(val >> 128) as bv128);
      write_bv128(mem',address+16,(val & 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF) as bv128)
    }

    /**
     * Write a byte to a given address in Memory.
     */
    function method write_u8(mem:T, address:u256, val:u8) : T {
        // Write location
        Memory(contents:=mem.contents[address:=val])
    }

    function method write_u256(mem:T, address:u256, val:u256) : T
    // Cannot write passed end of memory.
    requires (address as int) + 31 <= MAX_UINT256 {
      write_bv256(mem,address,val as bv256)
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
