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
    const TWO_7   : int := 0x0_80;
    const TWO_8   : int := 0x1_00;
    const TWO_15  : int := 0x0_8000;
    const TWO_16  : int := 0x1_0000;
    const TWO_24  : int := 0x1_0000_00;
    const TWO_31  : int := 0x0_8000_0000;
    const TWO_32  : int := 0x1_0000_0000;
    const TWO_40  : int := 0x1_0000_0000_00;
    const TWO_48  : int := 0x1_0000_0000_0000;
    const TWO_56  : int := 0x1_0000_0000_0000_00;
    const TWO_63  : int := 0x0_8000_0000_0000_0000;
    const TWO_64  : int := 0x1_0000_0000_0000_0000;
    const TWO_127 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000;
    const TWO_128 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000;
    const TWO_160 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;
    const TWO_255 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;
    const TWO_256 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;

    // Signed Integers
    const MIN_I8   : int := -TWO_7;
    const MAX_I8   : int :=  TWO_7 - 1;
    const MIN_I16  : int := -TWO_15;
    const MAX_I16  : int :=  TWO_15 - 1;
    const MIN_I32  : int := -TWO_31;
    const MAX_I32  : int :=  TWO_31 - 1;
    const MIN_I64  : int := -TWO_63;
    const MAX_I64  : int :=  TWO_63 - 1;
    const MIN_I128 : int := -TWO_127;
    const MAX_I128 : int :=  TWO_127 - 1;
    const MIN_I256 : int := -TWO_255;
    const MAX_I256 : int :=  TWO_255 - 1;

    newtype{:nativeType "sbyte"} i8 = i:int   | MIN_I8 <= i <= MAX_I8
    newtype{:nativeType "short"} i16 = i:int  | MIN_I16 <= i <= MAX_I16
    newtype{:nativeType "int"}   i32 = i:int  | MIN_I32 <= i <= MAX_I32
    newtype{:nativeType "long"}  i64 = i:int  | MIN_I64 <= i <= MAX_I64
    newtype i128 = i:int | MIN_I128 <= i <= MAX_I128
    newtype i256 = i:int | MIN_I256 <= i <= MAX_I256

    // Unsigned Integers
    const MAX_U8 : int :=  TWO_8 - 1;
    const MAX_U16 : int := TWO_16 - 1;
    const MAX_U24 : int := TWO_24 - 1;
    const MAX_U32 : int := TWO_32 - 1;
    const MAX_U40 : int := TWO_40 - 1;
    const MAX_U48 : int := TWO_48 - 1;
    const MAX_U56 : int := TWO_56 - 1;
    const MAX_U64 : int := TWO_64 - 1;
    const MAX_U128 : int := TWO_128 - 1;
    const MAX_U160: int := TWO_160 - 1;
    const MAX_U256: int := TWO_256 - 1

    newtype{:nativeType "byte"} u8 = i:int    | 0 <= i <= MAX_U8
    newtype{:nativeType "ushort"} u16 = i:int | 0 <= i <= MAX_U16
    newtype{:nativeType "uint"} u24 = i:int | 0 <= i <= MAX_U24
    newtype{:nativeType "uint"} u32 = i:int   | 0 <= i <= MAX_U32
    newtype{:nativeType "ulong"} u40 = i:int   | 0 <= i <= MAX_U40
    newtype{:nativeType "ulong"} u48 = i:int   | 0 <= i <= MAX_U48
    newtype{:nativeType "ulong"} u56 = i:int   | 0 <= i <= MAX_U56
    newtype{:nativeType "ulong"} u64 = i:int  | 0 <= i <= MAX_U64
    newtype u128 = i:int | 0 <= i <= MAX_U128
    newtype u160 = i:int | 0 <= i <= MAX_U160
    newtype u256 = i:int | 0 <= i <= MAX_U256


    // Determine maximum of two u256 integers.
    function method Max(i1: int, i2: int) : int {
        if i1 >= i2 then i1 else i2
    }

    // Round up a given number (i) by a given multiple (r).
    function method RoundUp(i: int, r: nat) : int
    requires r > 0 {
        if (i % r) == 0 then i
        else
        ((i/r)*r) + r
    }

    // =========================================================
    // Conversion to/from byte sequences
    // =========================================================

    function method ReadUint8(bytes: seq<u8>, address:nat) : u8
    requires address < |bytes| {
        bytes[address]
    }

    function method ReadUint16(bytes: seq<u8>, address:nat) : u16
    requires (address+1) < |bytes| {
        var b1 := bytes[address] as u16;
        var b2 := bytes[address+1] as u16;
        (b1 * (TWO_8 as u16)) + b2
    }

    function method ReadUint32(bytes: seq<u8>, address:nat) : u32
    requires (address+3) < |bytes| {
        var b1 := ReadUint16(bytes, address) as u32;
        var b2 := ReadUint16(bytes, address+2) as u32;
        (b1 * (TWO_16 as u32)) + b2
    }

    function method ReadUint64(bytes: seq<u8>, address:nat) : u64
    requires (address+7) < |bytes| {
        var b1 := ReadUint32(bytes, address) as u64;
        var b2 := ReadUint32(bytes, address+4) as u64;
        (b1 * (TWO_32 as u64)) + b2
    }

    // =========================================================
    // Exponent
    // =========================================================

    /**
     * Compute n^k.
     */
    function method Pow(n:nat, k:nat) : nat {
        if k == 0 then 1
        else if k == 1 then n
        else
            var p := k / 2;
            var np := Pow(n,p);
            if p*2 == k then np * np
            else np * np * n
    }

    // Simple lemma about POW.
    lemma lemma_pow2(k:nat)
    ensures Pow(2,k) > 0 {
        if k == 0 {
            assert Pow(2,k) == 1;
        } else if k == 1 {
            assert Pow(2,k) == 2;
        } else {
            lemma_pow2(k/2);
        }
    }

    // =========================================================
    // Non-Euclidean Division / Remainder
    // =========================================================

    // This provides a non-Euclidean division operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  This operator, therefore,
    // always divides *towards* zero.
    function method Div(lhs: int, rhs: int) : int
    requires rhs != 0 {
        if lhs >= 0 then lhs / rhs
        else
        -((-lhs) / rhs)
    }

    // This provides a non-Euclidean Remainder operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  Observe that this is a
    // true Remainder operator, and not a modulus operator.  For
    // emxaple, this means the result can be negative.
    function method Rem(lhs: int, rhs: int) : int
    requires rhs != 0 {
        if lhs >= 0 then (lhs % rhs)
        else
        var d := -((-lhs) / rhs);
        lhs - (d * rhs)
    }
}

/**
 * Various helper methods related to unsigned 16bit integers.
 */
module U16 {
    import opened Int

    // Read nth 8bit word (i.e. byte) out of this u16, where 0
    // identifies the most significant byte.
    function method NthUint8(v:u16, k: nat) : u8
        // Cannot read more than two words!
    requires k < 2 {
        if k == 0
            then (v / (TWO_8 as u16)) as u8
        else
            (v % (TWO_8 as u16)) as u8
    }
}

/**
 * Various helper methods related to unsigned 32bit integers.
 */
module U32 {
    import opened Int

    // Read nth 16bit word out of this u32, where 0 identifies the most
    // significant word.
    function method NthUint16(v:u32, k: nat) : u16
        // Cannot read more than two words!
    requires k < 2 {
        if k == 0
            then (v / (TWO_16 as u32)) as u16
        else
            (v % (TWO_16 as u32)) as u16
    }
}

/**
 * Various helper methods related to unsigned 64bit integers.
 */
module U64 {
    import opened Int

    // Read nth 32bit word out of this u64, where 0 identifies the most
    // significant word.
    function method NthUint32(v:u64, k: nat) : u32
        // Cannot read more than two words!
    requires k < 2 {
        if k == 0
            then (v / (TWO_32 as u64)) as u32
        else
            (v % (TWO_32 as u64)) as u32
    }
}

/**
 * Various helper methods related to unsigned 128bit integers.
 */
module U128 {
    import opened Int

    // Read nth 64bit word out of this u128, where 0 identifies the most
    // significant word.
    function method NthUint64(v:u128, k: nat) : u64
        // Cannot read more than two words!
    requires k < 2 {
        if k == 0
            then (v / (TWO_64 as u128)) as u64
        else
            (v % (TWO_64 as u128)) as u64
    }
}

/**
 * Various helper methods related to unsigned 256bit integers.
 */
module U256 {
    import opened Int
    import U128
    import U64
    import U32
    import U16

    function method Shl(lhs: u256, rhs: u256) : u256 {
        var lbv := lhs as bv256;
        // NOTE: unclear whether shifting is optimal choice here.
        var res := if rhs < 256 then (lbv << rhs) else 0;
        //
        res as u256
    }

    function method Shr(lhs: u256, rhs: u256) : u256 {
        var lbv := lhs as bv256;
        // NOTE: unclear whether shifting is optimal choice here.
        var res := if rhs < 256 then (lbv >> rhs) else 0;
        //
        res as u256
    }

    // Read nth 128bit word out of this u256, where 0 identifies the most
    // significant word.
    function method NthUint128(v:u256, k: nat) : u128
        // Cannot read more than two words!
        requires k < 2 {
        if k == 0
            then (v / (TWO_128 as u256)) as u128
        else
            (v % (TWO_128 as u256)) as u128
    }

    // Read nth byte out of this u256, where 0 identifies the most
    // significant byte.
    function method NthUint8(v:u256, k: nat) : u8
        // Cannot read more than 32bytes!
        requires k < 32 {
        // This is perhaps a tad ugly.  Happy to take suggestions on
        // a better approach :)
        var w128 := NthUint128(v,k / 16);
        var w64 := U128.NthUint64(w128,(k % 16) / 8);
        var w32 :=  U64.NthUint32(w64,(k % 8) / 4);
        var w16 :=  U32.NthUint16(w32,(k % 4) / 2);
        U16.NthUint8(w16,k%2)
    }
}

module I256 {
    import U256
    import Word
    import opened Int

    // This provides a non-Euclidean division operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  This operator, therefore,
    // always divides *towards* zero.
    function method div(lhs: i256, rhs: i256) : i256
        // Cannot divide by zero!
        requires rhs != 0
        // Range restriction to prevent overflow
        requires (rhs != -1 || lhs != (-TWO_255 as i256)) {
        Int.Div(lhs as int, rhs as int) as i256
    }

    // This provides a non-Euclidean Remainder operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  Observe that this is a
    // true Remainder operator, and not a modulus operator.  For
    // emxaple, this means the result can be negative.
    function method Rem(lhs: i256, rhs: i256) : i256
        // Cannot divide by zero!
        requires rhs != 0 {
        Int.Rem(lhs as int, rhs as int) as i256
    }

    // Shift Arithmetic Right using Bitshifts
    function method Sar(lhs: i256, rhs: u256) : u256 {
        if lhs >= 0 then
            // Easy case, unsigned shr sufficient.
            U256.Shr(lhs as u256, rhs)
        else if rhs > 256 then MAX_U256 as u256
        else
            // Determine mask
            var mask := (MAX_U256 as bv256) << (256 - rhs);
            var lbv := (Word.fromI256(lhs) as bv256 >> rhs);
            (mask | lbv) as u256
    }

    // Shift Arithmetic Right.  This implementation follows the Yellow Paper quite
    // accurately.  However, it performs very poorly when translated into Java.
    function method Sar2(lhs: i256, rhs: u256) : i256 {
        if rhs == 0 then lhs
        else
            var r := Int.Pow(2,rhs as nat);
            lemma_pow2(rhs as nat);
            ((lhs as int) / r) as i256
    }
}

module Word {
  import opened Int

  // Decode a 256bit word as a signed 256bit integer.  Since words
  // are represented as u256, the parameter has type u256.  However,
  // its important to note that this does not mean the value in
  // question represents an unsigned 256 bit integer.  Rather, it is a
  // signed integer encoded into an unsigned integer.
  function method asI256(w: u256) : i256 {
    if w > (MAX_I256 as u256)
    then
      var v := 1 + MAX_U256 - (w as int);
      (-v) as i256
    else
      w as i256
  }

  // Encode a 256bit signed integer as a 256bit word.  Since words are
  // represented as u256, the return is represented as u256.  However,
  // its important to note that this does not mean the value in
  // question represents an unsigned 256 bit integer.  Rather, it is a
  // signed integer encoded into an unsigned integer.
  function method fromI256(w: Int.i256) : u256 {
    if w < 0
    then
      var v := 1 + MAX_U256 + (w as int);
      v as u256
    else
      w as u256
  }
}
