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
include "../util/bytes.dfy"
include "../util/int.dfy"

module Code {
  import Bytes
  import opened Int

  // =============================================================================
  // Code Segment
  // =============================================================================

  const MAX_CODE_SIZE := 24576

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

  function method DecodeUint8(c:T, address:nat) : u8 {
    // Read word at given location
    if address < |c.contents| then c.contents[address]
    else 0 // Opcodes.STOP
  }

  function method CodeAt(c: T, index: nat): u8
  requires 0 <= index < Size(c) as nat {
    c.contents[index]
  }

  /**
   * Slice out a subsequence of bytes from a given sequence.
   * If the requested subsequence overflows available memory,
   * it is padded out with zeros.
   */
  function method Slice(c:T, address:nat, len:nat) : seq<u8> {
    Bytes.Slice(c.contents,address,len)
  }
}
