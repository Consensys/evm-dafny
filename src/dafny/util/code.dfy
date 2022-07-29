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

  const MAX_CODE_SIZE := 42_000_000

  /**
   * A code segment is just a sequence of words which form the
   * opcodes and operands of the machine instructions.
   */
  datatype Raw = Code(contents:seq<u8>)

  type T = c:Raw | |c.contents| <= MAX_CODE_SIZE witness Code([])

  /**
   * Create a code segment from an initial sequence of words.
   */
  function method Create(contents:seq<u8>) : T
    requires |contents| <= MAX_CODE_SIZE {
        Code(contents:=contents)
  }

  /**
   * Get the size of this code segment.
   */
  function method Size(c:T) : u256 { |c.contents| as u256 }

  function method DecodeUint8(c:T, address:nat) : u8
    // Decode position must be valid.
    requires address < |c.contents| {
      // Read word at given location
      c.contents[address]
  }

  function method DecodeUint16(c:T, address:nat) : u16
    // Decode position must be valid.
    requires address+1 < |c.contents| {
      var k1 := DecodeUint8(c,address) as u16;
      var k2 := DecodeUint8(c,address+1) as u16;
      (k1 * 256) + k2
  }
}
