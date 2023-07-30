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
include "arrays.dfy"

module ByteUtils {
    import opened Int
    import Arrays

    /**
     * Read the byte at a given address in Memory.  If the given location
     * has not been initialised, then zero is returned as default.
     */
    function ReadUint8(mem:seq<u8>, address:nat) : u8 {
        // Read location
        if address < |mem|
        then
          mem[address]
        else
          0
    }

    /**
     * Read a 16bit word from a given address in Memory assuming
     * big-endian addressing.  If the read overflows the available
     * data, then it is padded with zeros.
     */
    function ReadUint16(mem:seq<u8>, address:nat) : u16 {
        var w1 := ReadUint8(mem,address) as u16;
        var w2 := ReadUint8(mem,address+1) as u16;
        (w1 * (TWO_8 as u16)) + w2
    }

    /**
     * Read a 32bit word from a given address in Memory assuming
     * big-endian addressing.
     */
    function ReadUint32(mem:seq<u8>, address:nat) : u32 {
        var w1 := ReadUint16(mem,address) as u32;
        var w2 := ReadUint16(mem,address+2) as u32;
        (w1 * (TWO_16 as u32)) + w2
    }

    /**
     * Read a 64bit word from a given address in Memory assuming
     * big-endian addressing.  If the read overflows the available
     * data, then it is padded with zeros.
     */
    function ReadUint64(mem:seq<u8>, address:nat) : u64 {
        var w1 := ReadUint32(mem,address) as u64;
        var w2 := ReadUint32(mem,address+4) as u64;
        (w1 * (TWO_32 as u64)) + w2
    }

    /**
     * Read a 128bit word from a given address in Memory assuming
     * big-endian addressing.  If the read overflows the available
     * data, then it is padded with zeros.
     */
    function ReadUint128(mem:seq<u8>, address:nat) : u128 {
        var w1 := ReadUint64(mem,address) as u128;
        var w2 := ReadUint64(mem,address+8) as u128;
        (w1 * (TWO_64 as u128)) + w2
    }

    /**
     * Read a 256bit word from a given address in Memory assuming
     * big-endian addressing.  If the read overflows the available
     * data, then it is padded with zeros.
     */
    function ReadUint256(mem:seq<u8>, address:nat) : u256 {
        var w1 := ReadUint128(mem,address) as u256;
        var w2 := ReadUint128(mem,address+16) as u256;
        (w1 * (TWO_128 as u256)) + w2
    }

    /**
     * Write a byte to a given address in Memory.
     */
    function WriteUint8(mem:seq<u8>, address:nat, val:u8) : (mem':seq<u8>)
    requires address < |mem|
    ensures Arrays.EqualsExcept(mem,mem',address,1){
        // Write location
        mem[address:=val]
    }

    /**
     * Write a 16bit word to a given address in Memory using
     * big-endian addressing.
     */
    function WriteUint16(mem:seq<u8>, address:nat, val:u16) : (mem':seq<u8>)
    requires address + 1 < |mem|
    ensures Arrays.EqualsExcept(mem,mem',address,2){
      var w1 := val / (TWO_8 as u16);
      var w2 := val % (TWO_8 as u16);
      var mem' := WriteUint8(mem,address,w1 as u8);
      WriteUint8(mem',address+1,w2 as u8)
    }

    /**
     * Write a 32bit word to a given address in Memory using
     * big-endian addressing.
     */
    function WriteUint32(mem:seq<u8>, address:nat, val:u32) : (mem':seq<u8>)
    requires address + 3 < |mem|
    ensures Arrays.EqualsExcept(mem,mem',address,4){
      var w1 := val / (TWO_16 as u32);
      var w2 := val % (TWO_16 as u32);
      var mem' := WriteUint16(mem,address,w1 as u16);
      WriteUint16(mem',address+2,w2 as u16)
    }

    /**
     * Write a 64bit word to a given address in Memory using
     * big-endian addressing.
     */
    function WriteUint64(mem:seq<u8>, address:nat, val:u64) : (mem':seq<u8>)
    requires address + 7 < |mem|
    ensures Arrays.EqualsExcept(mem,mem',address,8) {
      var w1 := val / (TWO_32 as u64);
      var w2 := val % (TWO_32 as u64);
      var mem' := WriteUint32(mem,address,w1 as u32);
      WriteUint32(mem',address+4,w2 as u32)
    }

    /**
     * Write a 128bit word to a given address in Memory using
     * big-endian addressing.
     */
    function WriteUint128(mem:seq<u8>, address:nat, val:u128) : (mem':seq<u8>)
    requires address + 15 < |mem|
    ensures Arrays.EqualsExcept(mem,mem',address,16) {
      var w1 := val / (TWO_64 as u128);
      var w2 := val % (TWO_64 as u128);
      var mem' := WriteUint64(mem,address,w1 as u64);
      WriteUint64(mem',address+8,w2 as u64)
    }

    /**
     * Write a 256bit word to a given address in Memory using
     * big-endian addressing.
     */
    function WriteUint256(mem:seq<u8>, address:nat, val:u256) : (mem':seq<u8>)
    requires address + 31 < |mem|
    ensures Arrays.EqualsExcept(mem,mem',address,32) {
      var w1 := val / (TWO_128 as u256);
      var w2 := val % (TWO_128 as u256);
      var mem' := WriteUint128(mem,address,w1 as u128);
      WriteUint128(mem',address+16,w2 as u128)
    }

    /** Converts a sequence of bytes into a u256.
     *
     *  @param  bytes   A sequence of bytes.
     *  @returns        The big-endian and 0-left-padded value on 256 bits.
     */
    function ConvertBytesTo256(bytes: seq<u8>): u256
        requires 0 < |bytes| <= 32
    {
        if |bytes| == 1 then (bytes[0] as u256)
        else if |bytes| == 2 then (ReadUint16(bytes,0) as u256)
        else if |bytes| <= 4 then (ReadUint32(LeftPad(bytes,4),0) as u256)
        else if |bytes| <= 8 then (ReadUint64(LeftPad(bytes,8),0) as u256)
        else if |bytes| <= 16 then (ReadUint128(LeftPad(bytes,16),0) as u256)
        else ReadUint256(LeftPad(bytes,32),0)
    }

    /**
     * Pad an array of bytes with zeros in the low addresses upto a given
     * size n.
     */
    function LeftPad(bytes:seq<u8>, n:nat) : seq<u8>
    requires |bytes| <= n {
        // Calculate padding required
        var k := n - |bytes|;
        // Append it!
        Padding(k) + bytes
    }

    /**
     * Construct a sequence of an arbitrary sized padded out with zeros.
     */
    function Padding(n:nat) : seq<u8>
    ensures |Padding(n)| == n
    {
        seq(n, i => 0)
    }

}
