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
}
