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
  const MAX_U8 : int :=  0x1_00 - 1;
  const MAX_U16 : int := 0x1_0000 - 1;
  const MAX_U32 : int := 0x1_0000_0000 - 1;
  const MAX_U64 : int := 0x10000000000000000 - 1;
  const MAX_UINT128 : int :=  0x1_0000_0000_0000_0000_0000_0000_0000_0000 - 1;
  const MAX_UINT160: int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 - 1;
  const MAX_UINT256: int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 - 1

  newtype{:nativeType "byte"} u8 = i:int    | 0 <= i <= MAX_U8
  newtype{:nativeType "ushort"} u16 = i:int | 0 <= i <= MAX_U16
  newtype{:nativeType "uint"} u32 = i:int   | 0 <= i <= MAX_U32
  newtype{:nativeType "ulong"} u64 = i:int  | 0 <= i <= MAX_U64
  newtype u128 = i:int | 0 <= i <= MAX_UINT128
  newtype u160 = i:int | 0 <= i <= MAX_UINT160
  newtype u256 = i:int | 0 <= i <= MAX_UINT256
}
