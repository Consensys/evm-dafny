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

module Code {
  import opened Int

  // =============================================================================
  // Code Segment
  // =============================================================================

  /**
   * A code segment is just a sequence of words which form the
   * opcodes and operands of the machine instructions.
   */
  datatype Raw = Code(contents:seq<u8>)

  type T = c:Raw | |c.contents| <= MAX_U256 witness Code([])

  /**
   * Create a code segment from an initial sequence of words.
   */
  function method create(contents:seq<u8>) : T
    requires |contents| <= MAX_U256 {
        Code(contents:=contents)
  }

  /**
   * Get the size of this code segment.
   */
  function method size(c:T) : u256 { |c.contents| as u256 }

  function method decode_u8(c:T, pc:u256) : u8
    // Decode position must be valid.
    requires pc < size(c) {
      // Read word at given location
      c.contents[pc]
  }
}
