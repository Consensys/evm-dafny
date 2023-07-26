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

include "option.dfy"

module Int {
    import opened Optional

    const TWO_7   : int := 0x0_80
    const TWO_8   : int := 0x1_00
    const TWO_15  : int := 0x0_8000
    const TWO_16  : int := 0x1_0000
    const TWO_24  : int := 0x1_0000_00
    const TWO_31  : int := 0x0_8000_0000
    const TWO_32  : int := 0x1_0000_0000
    const TWO_40  : int := 0x1_0000_0000_00
    const TWO_48  : int := 0x1_0000_0000_0000
    const TWO_56  : int := 0x1_0000_0000_0000_00
    const TWO_63  : int := 0x0_8000_0000_0000_0000
    const TWO_64  : int := 0x1_0000_0000_0000_0000
    const TWO_127 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000
    const TWO_128 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_160 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_255 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_256 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000

    // Signed Integers
    const MIN_I8   : int := -TWO_7
    const MAX_I8   : int :=  TWO_7 - 1
    const MIN_I16  : int := -TWO_15
    const MAX_I16  : int :=  TWO_15 - 1
    const MIN_I32  : int := -TWO_31
    const MAX_I32  : int :=  TWO_31 - 1
    const MIN_I64  : int := -TWO_63
    const MAX_I64  : int :=  TWO_63 - 1
    const MIN_I128 : int := -TWO_127
    const MAX_I128 : int :=  TWO_127 - 1
    const MIN_I256 : int := -TWO_255
    const MAX_I256 : int :=  TWO_255 - 1

    newtype{:nativeType "sbyte"} i8 = i:int   | MIN_I8 <= i <= MAX_I8
    newtype{:nativeType "short"} i16 = i:int  | MIN_I16 <= i <= MAX_I16
    newtype{:nativeType "int"}   i32 = i:int  | MIN_I32 <= i <= MAX_I32
    newtype{:nativeType "long"}  i64 = i:int  | MIN_I64 <= i <= MAX_I64
    newtype i128 = i:int | MIN_I128 <= i <= MAX_I128
    newtype i256 = i:int | MIN_I256 <= i <= MAX_I256

    // Unsigned Integers
    const MAX_U8 : int :=  TWO_8 - 1
    const MAX_U16 : int := TWO_16 - 1
    const MAX_U24 : int := TWO_24 - 1
    const MAX_U32 : int := TWO_32 - 1
    const MAX_U40 : int := TWO_40 - 1
    const MAX_U48 : int := TWO_48 - 1
    const MAX_U56 : int := TWO_56 - 1
    const MAX_U64 : int := TWO_64 - 1
    const MAX_U128 : int := TWO_128 - 1
    const MAX_U160: int := TWO_160 - 1
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

    // Compute absolute value
    function Abs(x: int) : nat {
        if x >= 0 then x else -x
    }

    // Determine maximum of two u256 integers.
    function Max(i1: int, i2: int) : int {
        if i1 >= i2 then i1 else i2
    }

    // Determine maximum of two u256 integers.
    function Min(i1: int, i2: int) : int {
        if i1 < i2 then i1 else i2
    }

    // Round up a given number (i) by a given multiple (r).
    function RoundUp(i: int, r: nat) : int
    requires r > 0 {
        if (i % r) == 0 then i
        else
            ((i/r)*r) + r
    }

    // Return the maximum value representable using exactly n unsigned bytes.
    // This is essentially computing (2^n - 1).  However, the point of doing it
    // in this fashion is to avoid using Pow() as this is challenging for the
    // verifier.
    function MaxUnsignedN(n:nat) : (r:nat)
    requires 1 <= n <= 32 {
        match n
            case 1 => MAX_U8
            case 2 => MAX_U16
            case 3 => MAX_U24
            case 4 => MAX_U32
            case 5 => MAX_U40
            case 6 => MAX_U48
            case 7 => MAX_U56
            case 8 => MAX_U64
            case 16 => MAX_U128
            case 20 => MAX_U160
            case 32 => MAX_U256
            // Fall back case (for now)
            case _ => Pow(2,n) - 1
    }

    // =========================================================
    // Exponent
    // =========================================================

    /**
     * Compute n^k.
     */
    function Pow(n:nat, k:nat) : (r:nat)
    // Following needed for some proofs
    ensures n > 0 ==> r > 0 {
        if k == 0 then 1
        else if k == 1 then n
        else
            var p := k / 2;
            var np := Pow(n,p);
            if p*2 == k then np * np
            else
                np * np * n
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

    /**
     * Compute n^k % m.  This is more efficient that doing Pow(n,k) % m.  In
     * essence, this works by recursive decomposing the work and squaring the
     * results.
     */
    function ModPow(n:nat, k:nat, m:nat) : (r:nat)
    requires m > 0
    ensures r < m
    ensures n > 0 ==> r >= 0
    decreases k {
        var nm := n % m;
        if k == 0 || m == 1 then 1%m
        else if k == 1 then nm
        else
            var np := ModPow(nm,k/2,m);
            var np2 := (np * np) % m;
            if (k%2) == 0 then
                // Even case.  n^2k = n^k * n^k
                np2
            else
                // Odd case.  n^2k+1 = n^2k * n
                (np2 * nm) % m
    }

    // Euclid's extended GCD algorithm, implemented recursively.
    function GcdExtended(a: nat, b: nat) : (r:(nat,int,int))
    // Conditions under which gcd is non-zero
    ensures b > 0 ==> r.0 > 0
    // Bezout's identity
    ensures (a*r.1)+(b*r.2) == r.0 {
        if a == 0 then (b,0,1)
        else
            var (g,x,y) := GcdExtended(b%a,a);
            (g,y-((b/a)*x),x)
    }

    /// Determine multiplicative inverse of an element a under mod n.
    function Inverse(a: nat, n: nat) : (r:Option<nat>)
    requires a < n {
        var (gcd,x,y) := GcdExtended(a,n);
        if gcd > 1 then None
        else if x >= 0 then Some(x)
        else
            // Following property is known to hold for Euclid's extended
            // algorithm.  Unfortunately, I did not yet figure out how to get
            // Dafny to prove this for us.
            assume {:axiom} Abs(x) < n;
            // Done
            Some(x+n)
    }

    // A prime number is a natural greater than 1 that is divisible by any
    // smaller number (except 1).
    predicate IsPrime(n: nat) {
        n > 1 && forall a :: 1 <= a < n ==> GcdExtended(a,n).0 == 1
    }

    // Every element in a prime field has a multiplicative inverse.
    lemma PrimeFieldsHaveInverse(a:nat, n: nat)
    requires IsPrime(n)
    requires 1 <= a < n
    ensures Inverse(a,n) != None {
        assert GcdExtended(a,n).0 == 1;
    }

    // =========================================================
    // Non-Euclidean Division / Remainder
    // =========================================================

    // This provides a non-Euclidean division operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  This operator, therefore,
    // always divides *towards* zero.
    function Div(lhs: int, rhs: int) : int
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
    function Rem(lhs: int, rhs: int) : int
    requires rhs != 0 {
        if lhs >= 0 then (lhs % rhs)
        else
            var d := -((-lhs) / rhs);
            lhs - (d * rhs)
     }

    // Convert an arbitrary sized unsigned integer into a sequence of 1 or more
    // bytes in big endian notation.  This is naturally a tail recursive
    // function.
    function {:tailrecursion true} ToBytes(v:nat) : (r:seq<u8>)
    ensures |r| > 0 {
        // Extract the byte
        var byte : u8 := (v % 256) as u8;
        // Determine what's left
        var w : nat := v/256;
        if w == 0 then [byte]
        else
            ToBytes(w) + [byte]
    }

    // Convert a given sequence of zero or more bytes into an arbitrary sized
    // unsigned integer.  If the empty sequence is given, then zero is returned.
    // This is implemented by method to ensure large sequences can be converted
    // without overflowing the stack.
    function FromBytes(bytes:seq<u8>) : (r:nat) {
        if |bytes| == 0 then 0
        else
            var last := |bytes| - 1;
            var byte := bytes[last] as nat;
            var msw := FromBytes(bytes[..last]);
            (msw * 256) + byte
    } by method {
        r := 0;
        for i := 0 to |bytes|
        invariant r == FromBytes(bytes[..i]) {
            var ith := bytes[i] as nat;
            r := (r * 256) + ith;
            LemmaFromBytes(bytes,i);
        }
        // Dafny needs help here :)
        assert bytes[..|bytes|] == bytes;
        // Done
        return r;
    }

    // Lemma connecting FromBytes at an arbitrary position within a sequence.
    lemma LemmaFromBytes(bytes:seq<u8>,i:nat)
    requires 0 <= i < |bytes|
    ensures FromBytes(bytes[..i+1]) == (FromBytes(bytes[..i]) * 256) + bytes[i] as nat {
        if i != 0 {
            var cons := bytes[..i+1];
            var tail := bytes[..i];
            var head := bytes[i];
            // For reasons unknown, Dafny cannot figure this out for itself.
            assert (cons == tail + [head]);
        }
    }

    // Sanity check that going to/from bytes gives identical result.
    lemma LemmaFromToBytes(v: nat)
    ensures FromBytes(ToBytes(v)) == v {}

    // Sanity check for the other direction.  Observe that we require an
    // additional constraint because, in fact, in general the lemma does not
    // hold. For example FromBytes([0,0]) == 0 but ToBytes(0) == [0].
    // Therefore, the additional constraint just prevents unnecessary leading
    // zeros.
    lemma LemmaToFromBytes(bytes:seq<u8>)
    requires |bytes| > 0 && (|bytes| == 1 || bytes[0] != 0)
    ensures ToBytes(FromBytes(bytes)) == bytes {
        var n := |bytes| - 1;
        if |bytes| > 1 {
            LemmaToFromBytes(bytes[..n]);
        }
    }

    // Lemma to help connect the expected byte length of two natural numbers.
    // For example, if one number is less than another then its byte sequence
    // will not be larger (though could be the same length).
    lemma LemmaLengthToBytes(n: nat, m: nat)
    requires n <= m
    ensures |ToBytes(n)| <= |ToBytes(m)| {}

    // Lemma to help connect the expected byte length of a natural number
    // through coecion.  Specifically, converting a byte sequence into a number
    // and then back again yields a byte sequence that is not longer than the
    // original.  Observer, however, that it can be shorter if there are leading
    // zeros in the original byte sequence.
    lemma LemmaLengthFromBytes(n: nat, bytes: seq<u8>)
    requires n == FromBytes(bytes)
    ensures bytes == [] || |ToBytes(n)| <= |bytes| {
        if |bytes| == 1 {
            assert |ToBytes(n)| == 1;
        } else if |bytes| > 1 {
            var last := |bytes| - 1;
            var tail := bytes[..last];
            LemmaLengthFromBytes(n/256,tail);
        }
    }
}

/**
 * Various helper methods related to unsigned 8bit integers.
 */
module U8 {
    import opened Int

    // Compute the log of a value at base 2 where the result is rounded down.
    function Log2(v:u8) : (r:nat)
        ensures r < 8 {
        // Split 4 bits
        if v <= 15 then
            // Split 2 bits
            if v <= 3 then
                // Split 1 bit
                if v <= 1 then 0 else 1
            else
                // Split 1 bit
                if v <= 7 then 2 else 3
        else
            // Split 2 bits
            if v <= 63 then
                // Split 1 bit
                if v <= 31 then 4 else 5
            else
                // Split 1 bit
                if v <= 127 then 6 else 7
    }
}

/**
 * Various helper methods related to unsigned 16bit integers.
 */
module U16 {
    import opened Int
    import U8

    // Read nth 8bit word (i.e. byte) out of this u16, where 0
    // identifies the most significant byte.
    function NthUint8(v:u16, k: nat) : u8
    // Cannot read more than two words!
    requires k < 2 {
        if k == 0 then (v / (TWO_8 as u16)) as u8
        else
            (v % (TWO_8 as u16)) as u8
    }

    /**
     * Compute the log of a value at base 2 where the result is rounded down.
     */
    function Log2(v:u16) : (r:nat)
    ensures r < 16 {
        var low := (v % (TWO_8 as u16)) as u8;
        var high := (v / (TWO_8 as u16)) as u8;
        if high != 0 then U8.Log2(high)+8 else U8.Log2(low)
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u16) : (r:nat)
    ensures r <= 1 {
        var low := (v % (TWO_8 as u16)) as u8;
        var high := (v / (TWO_8 as u16)) as u8;
        if high != 0 then 1 else 0
    }

    /**
     * Convert a u16 into a sequence of 2 bytes (in big endian representation).
     */
    function ToBytes(v:u16) : (r:seq<u8>)
    ensures |r| == 2 {
        var low := (v % (TWO_8 as u16)) as u8;
        var high := (v / (TWO_8 as u16)) as u8;
        [high,low]
    }

    function Read(bytes: seq<u8>, address:nat) : u16
    requires (address+1) < |bytes| {
        var b1 := bytes[address] as u16;
        var b2 := bytes[address+1] as u16;
        (b1 * (TWO_8 as u16)) + b2
    }
}

/**
 * Various helper methods related to unsigned 32bit integers.
 */
module U32 {
    import U16
    import opened Int

    // Read nth 16bit word out of this u32, where 0 identifies the most
    // significant word.
    function NthUint16(v:u32, k: nat) : u16
    // Cannot read more than two words!
    requires k < 2 {
        if k == 0
        then (v / (TWO_16 as u32)) as u16
        else
            (v % (TWO_16 as u32)) as u16
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log2(v:u32) : (r:nat)
    ensures r < 32 {
        var low := (v % (TWO_16 as u32)) as u16;
        var high := (v / (TWO_16 as u32)) as u16;
        if high != 0 then U16.Log2(high)+16 else U16.Log2(low)
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u32) : (r:nat)
    ensures r <= 3 {
        var low := (v % (TWO_16 as u32)) as u16;
        var high := (v / (TWO_16 as u32)) as u16;
        if high != 0 then U16.Log256(high)+2 else U16.Log256(low)
    }

    /**
     * Convert a u32 into a sequence of 4 bytes (in big endian representation).
     */
    function ToBytes(v:u32) : (r:seq<u8>)
    ensures |r| == 4 {
        var low := (v % (TWO_16 as u32)) as u16;
        var high := (v / (TWO_16 as u32)) as u16;
        U16.ToBytes(high) + U16.ToBytes(low)
    }

    function Read(bytes: seq<u8>, address:nat) : u32
    requires (address+3) < |bytes| {
        var b1 := U16.Read(bytes, address) as u32;
        var b2 := U16.Read(bytes, address+2) as u32;
        (b1 * (TWO_16 as u32)) + b2
    }
    }

/**
 * Various helper methods related to unsigned 64bit integers.
 */
module U64 {
    import U32
    import opened Int

    // Read nth 32bit word out of this u64, where 0 identifies the most
    // significant word.
    function NthUint32(v:u64, k: nat) : u32
    // Cannot read more than two words!
    requires k < 2 {
        if k == 0
        then (v / (TWO_32 as u64)) as u32
        else
            (v % (TWO_32 as u64)) as u32
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log2(v:u64) : (r:nat)
    ensures r < 64 {
        var low := (v % (TWO_32 as u64)) as u32;
        var high := (v / (TWO_32 as u64)) as u32;
        if high != 0 then U32.Log2(high)+32 else U32.Log2(low)
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u64) : (r:nat)
    ensures r <= 7 {
        var low := (v % (TWO_32 as u64)) as u32;
        var high := (v / (TWO_32 as u64)) as u32;
        if high != 0 then U32.Log256(high)+4 else U32.Log256(low)
    }

    /**
     * Convert a u64 into a sequence of 8bytes (in big endian representation).
     */
    function ToBytes(v:u64) : (r:seq<u8>)
    ensures |r| == 8 {
        var low := (v % (TWO_32 as u64)) as u32;
        var high := (v / (TWO_32 as u64)) as u32;
        U32.ToBytes(high) + U32.ToBytes(low)
    }

    function Read(bytes: seq<u8>, address:nat) : u64
    requires (address+7) < |bytes| {
        var b1 := U32.Read(bytes, address) as u64;
        var b2 := U32.Read(bytes, address+4) as u64;
        (b1 * (TWO_32 as u64)) + b2
    }
    }

/**
 * Various helper methods related to unsigned 128bit integers.
 */
module U128 {
    import U64
    import opened Int

    // Read nth 64bit word out of this u128, where 0 identifies the most
    // significant word.
    function NthUint64(v:u128, k: nat) : u64
    // Cannot read more than two words!
    requires k < 2 {
        if k == 0
        then (v / (TWO_64 as u128)) as u64
        else
            (v % (TWO_64 as u128)) as u64
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log2(v:u128) : (r:nat)
    ensures r < 128 {
        var low := (v % (TWO_64 as u128)) as u64;
        var high := (v / (TWO_64 as u128)) as u64;
        if high != 0 then U64.Log2(high)+64 else U64.Log2(low)
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u128) : (r:nat)
    ensures r <= 15 {
        var low := (v % (TWO_64 as u128)) as u64;
        var high := (v / (TWO_64 as u128)) as u64;
        if high != 0 then U64.Log256(high)+8 else U64.Log256(low)
    }

    /**
     * Convert a u128 into a sequence of 16bytes (in big endian representation).
     */
    function ToBytes(v:u128) : (r:seq<u8>)
    ensures |r| == 16 {
        var low := (v % (TWO_64 as u128)) as u64;
        var high := (v / (TWO_64 as u128)) as u64;
        U64.ToBytes(high) + U64.ToBytes(low)
    }

    function Read(bytes: seq<u8>, address:nat) : u128
    requires (address+15) < |bytes| {
        var b1 := U64.Read(bytes, address) as u128;
        var b2 := U64.Read(bytes, address+8) as u128;
        (b1 * (TWO_64 as u128)) + b2
    }
}

/**
 * Various helper methods related to unsigned 256bit integers.
 */
module U256 {
    import opened Int
    import U8
    import U16
    import U32
    import U64
    import U128

    /** An axiom stating that a bv256 converted as a nat is bounded by 2^256. */
    lemma {:axiom} as_bv256_as_u256(v: bv256)
        ensures v as nat < TWO_256

    function Shl(lhs: u256, rhs: u256) : u256
    {
        if rhs >= 256 then 0
        else
            var p := Pow(2,rhs as nat);
            var n := (lhs as nat) * p;
            (n % TWO_256) as u256
    }

    function Shr(lhs: u256, rhs: u256) : u256 {
        if rhs >= 256 then 0
        else
            var p := Pow(2, rhs as nat);
            var n := (lhs as nat) / p;
            n as u256
    }

    /**
     * Compute the log of a value at base 2, where the result in rounded down.
     * This effectively determines the position of the highest on bit.
     */
    function Log2(v:u256) : (r:nat)
    ensures r < 256 {
        var low := (v % (TWO_128 as u256)) as u128;
        var high := (v / (TWO_128 as u256)) as u128;
        if high != 0 then U128.Log2(high)+128 else U128.Log2(low)
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u256) : (r:nat)
    ensures r <= 31 {
        var low := (v % (TWO_128 as u256)) as u128;
        var high := (v / (TWO_128 as u256)) as u128;
        if high != 0 then U128.Log256(high)+16 else U128.Log256(low)
    }

    // Read nth 128bit word out of this u256, where 0 identifies the most
    // significant word.
    function NthUint128(v:u256, k: nat) : u128
    // Cannot read more than two words!
    requires k < 2 {
        if k == 0
        then (v / (TWO_128 as u256)) as u128
        else
        (v % (TWO_128 as u256)) as u128
    }

    // Read nth byte out of this u256, where 0 identifies the most
    // significant byte.
    function NthUint8(v:u256, k: nat) : u8
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

    function Read(bytes: seq<u8>, address:nat) : u256
    requires (address+31) < |bytes| {
        var b1 := U128.Read(bytes, address) as u256;
        var b2 := U128.Read(bytes, address+16) as u256;
        (b1 * (TWO_128 as u256)) + b2
    }

    /**
     * Convert a u256 into a sequence of 32bytes in big endian representation.
     */
    function ToBytes(v:u256) : (r:seq<u8>)
    ensures |r| == 32 {
        var low := (v % (TWO_128 as u256)) as u128;
        var high := (v / (TWO_128 as u256)) as u128;
        U128.ToBytes(high) + U128.ToBytes(low)
    }

    /**
     * Sign extend a given value (v) using the most significant bit (msb) of its
     * kth byte.  Consider this example for v:
     *
     *      23    16 15     8 7      0
     *     +--------+--------+--------+
     * ... |10111010|10010101|01000101|
     *     +--------+--------+--------+
     *
     * Then, perfoming a sign extend with k=0 gives:
     *
     *      23    16 15     8 7      0
     *     +--------+--------+--------+
     * ... |00000000|00000000|01000101|
     *     +--------+--------+--------+
     *
     * Since the msb of byte 0 is 0, everything above that is set to zero.  In
     * contrast, performing a sign extend of our original input with k=1 gives:
     *
     *      23    16 15     8 7      0
     *     +--------+--------+--------+
     * ... |11111111|10010101|01000101|
     *     +--------+--------+--------+
     *
     * Since, in this case, the msb of byte 1 is 1.
     */
    function SignExtend(v: u256, k: nat) : u256 {
        if k >= 31 then v
        else
            // Reinterpret k as big endian
            var ith := 31 - k;
            // Extract byte containing sign bit
            var byte := NthUint8(v,ith);
            // Replicate sign bit.
            var signs := if byte >= 128 then seq(31-k, i => 0xff)
                else seq(31-k, i => 0);
            // Extract unchanged bytes
            var bytes := ToBytes(v)[ith..];
            // Sanity check
            assert |signs + bytes| == 32;
            // Done
            Read(signs + bytes,0)
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
    function Div(lhs: i256, rhs: i256) : i256
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
    function Rem(lhs: i256, rhs: i256) : i256
    // Cannot divide by zero!
    requires rhs != 0 {
        Int.Rem(lhs as int, rhs as int) as i256
    }

    // Shift Arithmetic Right.  This implementation follows the Yellow Paper quite
    // accurately.
    function Sar(lhs: i256, rhs: u256): i256 {
        if rhs == 0 then lhs
        else if rhs < 256
        then
            assert 0 < rhs < 256;
            var r := Pow(2,rhs as nat);
            ((lhs as int) / (r as int)) as i256
        else if lhs < 0 then -1
        else 0
    }
}

module Word {
    import opened Int

    // Decode a 256bit word as a signed 256bit integer.  Since words
    // are represented as u256, the parameter has type u256.  However,
    // its important to note that this does not mean the value in
    // question represents an unsigned 256 bit integer.  Rather, it is a
    // signed integer encoded into an unsigned integer.
    function asI256(w: u256) : i256 {
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
    function fromI256(w: Int.i256) : u256 {
        if w < 0
        then
            var v := 1 + MAX_U256 + (w as int);
            v as u256
        else
            w as u256
    }
}
