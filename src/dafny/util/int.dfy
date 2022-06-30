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
module Int {
  // Powers of Two
  const TWO_8   : int := 0x1_00;
  const TWO_16  : int := 0x1_0000;
  const TWO_32  : int := 0x1_0000_0000;
  const TWO_64  : int := 0x1_0000_0000_0000_0000;
  const TWO_128 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000;
  const TWO_160 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;
  const TWO_256 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;

  // Signed Integers
  const MIN_I8  : int := -0x80;
  const MAX_I8  : int :=  0x80 - 1;
  const MIN_I16 : int := -0x8000;
  const MAX_I16 : int :=  0x8000 - 1;
  const MIN_I32 : int := -0x80000000;
  const MAX_I32 : int :=  0x80000000 - 1;
  const MIN_I64 : int := -0x8000000000000000;
  const MAX_I64 : int :=  0x8000000000000000 - 1;

  newtype{:nativeType "sbyte"} i8 = i:int   | MIN_I8 <= i <= MAX_I8
  newtype{:nativeType "short"} i16 = i:int  | MIN_I16 <= i <= MAX_I16
  newtype{:nativeType "int"}   i32 = i:int  | MIN_I32 <= i <= MAX_I32
  newtype{:nativeType "long"}  i64 = i:int  | MIN_I64 <= i <= MAX_I64

  // Unsigned Integers
  const MAX_U8 : int :=  TWO_8 - 1;
  const MAX_U16 : int := TWO_16 - 1;
  const MAX_U32 : int := TWO_32 - 1;
  const MAX_U64 : int := TWO_64 - 1;
  const MAX_UINT128 : int := TWO_128 - 1;
  const MAX_UINT160: int := TWO_160 - 1;
  const MAX_UINT256: int := TWO_256 - 1

  newtype{:nativeType "byte"} u8 = i:int    | 0 <= i <= MAX_U8
  newtype{:nativeType "ushort"} u16 = i:int | 0 <= i <= MAX_U16
  newtype{:nativeType "uint"} u32 = i:int   | 0 <= i <= MAX_U32
  newtype{:nativeType "ulong"} u64 = i:int  | 0 <= i <= MAX_U64
  newtype u128 = i:int | 0 <= i <= MAX_UINT128
  newtype u160 = i:int | 0 <= i <= MAX_UINT160
  newtype u256 = i:int | 0 <= i <= MAX_UINT256

  // =========================================================
  // Conversion to/from byte sequences
  // =========================================================

  function read_u8(bytes: seq<u8>, address:nat) : u8
  requires address < |bytes| {
    bytes[address]
  }

  function read_u16(bytes: seq<u8>, address:nat) : u16
  requires (address+1) < |bytes| {
    var b1 := bytes[address] as u16;
    var b2 := bytes[address+1] as u16;
    (b1 * (TWO_8 as u16)) + b2
  }

  function read_u32(bytes: seq<u8>, address:nat) : u32
  requires (address+3) < |bytes| {
    var b1 := read_u16(bytes, address) as u32;
    var b2 := read_u16(bytes, address+2) as u32;
    (b1 * (TWO_16 as u32)) + b2
  }

  function read_u64(bytes: seq<u8>, address:nat) : u64
  requires (address+7) < |bytes| {
    var b1 := read_u32(bytes, address) as u64;
    var b2 := read_u32(bytes, address+4) as u64;
    (b1 * (TWO_32 as u64)) + b2
  }
}
