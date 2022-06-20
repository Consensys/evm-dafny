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

    datatype Raw = Memory(contents:seq<u8>)

    type T = m:Raw | |m.contents| < MAX_UINT256
    witness Memory([])

    /**
     * Create a memory from an initial sequence of words.
     */
    function method create(contents:seq<u8>) : T
    requires |contents| < MAX_UINT256 {
        Memory(contents:=contents)
    }

    /**
     * Return the size of this memory (in bytes).
     */
    function size(mem:T) : u256 { |mem.contents| as u256 }

    /**
     * Read the byte at a given address in Memory.  This requires that the address
     * is within bounds of the Memory.
     */
    function read_u8(mem:T, address:u256) : u8
      // Address must be within bounds
      requires address < (|mem.contents| as u256) {
        // Read location
        mem.contents[address]
    }

    /**
     * Write a byte to a given address in Memory.  This requires that the address
     * is within bounds of the Memory.
     */
    function write_u8(mem:T, address:u256, val:u8) : T
      // Address must be within bounds
      requires address < (|mem.contents| as u256) {
        // Write location
        Memory(contents:=mem.contents[address:=val])
    }
}
