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
 * Storage on the EVM is a word-addressable (non-volatile) random access memory.
 */
module Storage {
    import opened Int

    // =============================================================================
    // Random Access Memory
    // =============================================================================

    datatype Raw = Storage(contents:seq<u256>)

    type T = m:Raw | |m.contents| < MAX_UINT256
    witness Storage([])

    /**
     * Create some storage from an initial sequence of words.
     */
    function method create(contents:seq<u256>) : T
    requires |contents| < MAX_UINT256 {
        Storage(contents:=contents)
    }

    /**
     * Return the size of this storage (in words).
     */
    function size(mem:T) : u256 { |mem.contents| as u256 }

    /**
     * Read the value at a given address in Storage.  This requires that the address
     * is within bounds of the Storage.
     */
    function read(mem:T, address:u256) : u256
      // Address must be within bounds
      requires address < size(mem) {
        // Read location
        mem.contents[address]
    }

    /**
     * Write a value to a given address in Storage.  This requires that the address
     * is within bounds of the Storage.
     */
    function write(mem:T, address:u256, val:u256) : T
      // Address must be within bounds
      requires address < size(mem) {
        // Write location
        Storage(contents:=mem.contents[address:=val])
    }
}
