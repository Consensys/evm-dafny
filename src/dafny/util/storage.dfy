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

    datatype T = Storage(contents:map<u256,u256>)

    /**
     * Create some storage from an initial sequence of words.
     */
    function method Create(contents:map<u256,u256>) : T {
        Storage(contents:=contents)
    }

    /**
     * Read the value at a given address in Storage.  If the given location
     * has not been initialised, then zero is returned as default.
     */
    function method Read(mem:T, address:u256) : u256 {
      if address in mem.contents
        then
        mem.contents[address]
      else
        0
    }

    /**
     * Write a value to a given address in Storage.
     */
    function method Write(mem:T, address:u256, val:u256) : T {
        Storage(contents:=mem.contents[address:=val])
    }
}
