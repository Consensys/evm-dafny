/*
 * Copyright 2021 ConsenSys Software Inc.
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

  
/**
  * Define useful types.
  * This module is copied from IronFleet source code.
  * @link{https://github.com/microsoft/Ironclad}
 */
module NativeTypes {

    /** @note: newtype N = x: M | Q
     *  where:
     *      M is the base type i.e. is a numeric type and 
     *      Q is a boolean expression that can use x as a free variable.
     *  @see section 19 of references manual.
     *  @see section 24.1.11 for semantics of nativeType.
     *    newtype{:nativeType "long"} int64 means: use the integral type long (built-in Dafny)
     *    to represent the type  i:int | -0x8000000000000000 <= i < 0x8000000000000000
     */

    /* Signed and unsigned int. */
    newtype{:nativeType "sbyte"} sbyte = i:int | -0x80 <= i < 0x80
    newtype{:nativeType "byte"} uint8 = i:int | 0 <= i < 0x100
    newtype{:nativeType "short"} int16 = i:int | -0x8000 <= i < 0x8000
    newtype{:nativeType "ushort"} uint16 = i:int | 0 <= i < 0x10000
    newtype{:nativeType "int"} int32 = i:int | -0x80000000 <= i < 0x80000000
    newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000
    newtype{:nativeType "long"} int64 = i:int | -0x8000000000000000 <= i < 0x8000000000000000
    newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000
    
    /* Unsigned int (nats). */
    newtype{:nativeType "sbyte"} nat8 = i:int | 0 <= i < 0x80
    newtype{:nativeType "short"} nat16 = i:int | 0 <= i < 0x8000
    newtype{:nativeType "int"} nat32 = i:int | 0 <= i < 0x80000000
    newtype{:nativeType "long"} nat64 = i:int | 0 <= i < 0x8000000000000000

    const MAX_UINT8 := 0x100 - 1
}