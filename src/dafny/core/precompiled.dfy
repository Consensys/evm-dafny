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
include "../util/extern.dfy"
include "../util/arrays.dfy"
include "../util/int.dfy"
include "../util/option.dfy"

/**
 * Interface for the so-called "precompiled contracts".
 */
module Precompiled {
    import opened Int
    import opened Arrays
    import opened Optional
    import U32
    import U256
    import External
    import Bytes

    function Call(address: u160, data: Array<u8>) : Option<(Array<u8>,nat)>
    requires address >= 1 && address <= 9 {
        match address
        case 1 => CallEcdsaRecover(data)
        case 2 => CallSha256(data)
        case 3 => CallRipEmd160(data)
        case 4 => CallID(data)
        case 5 => CallModExp(data)
        case 6 => CallBnAdd(data)
        case 7 => CallBnMul(data)
        case 8 => CallSnarkV(data)
        case 9 => CallBlake2f(data)
    }

    // ========================================================================
    // (1) ECDSA Recover
    // ========================================================================
    const G_ECDSA := 3000;
    /**
     * Constant as defined in the Yellow Paper
     */
    const SECP256K1N : u256 := 115792089237316195423570985008687907852837564279074904382605163141518161494337;
    /**
     * Key recovery.
     */
    function CallEcdsaRecover(data: Array<u8>) : Option<(Array<u8>,nat)> {
        var h := Arrays.SliceAndPad(data,0,32,0);
        var v := Bytes.ReadUint256(data,32);
        var r := Bytes.ReadUint256(data,64);
        var s := Bytes.ReadUint256(data,96);
        // Sanity checks
        var key : Array<u8> := if !(v in {27,28}) || r == 0 || r >= SECP256K1N || s == 0 || s >= SECP256K1N
        then
            []
        else
            External.ECDSARecover(h,v as u8,r,s);
        //
        Some((key, G_ECDSA))
    }

    // ========================================================================
    // (2) SHA256
    // ========================================================================

    /**
     * SHA256
     */
    function CallSha256(data: Array<u8>) : Option<(Array<u8>,nat)> {
        Some((External.sha256(data),CostSha256(data)))
    }

    /**
     * Gas cost for sha256.
     */
    function CostSha256(data: Array<u8>) : nat {
        // Determine number of words required to cover data.
        var d := (Int.RoundUp(|data|,32)/32);
        // Done
        60 + (12 * d)
    }

    // ========================================================================
    // (3) RIPEMD160
    // ========================================================================

    /**
     * RipEmd160
     */
    function CallRipEmd160(data: Array<u8>) : Option<(Array<u8>,nat)> {
        Some((External.ripEmd160(data), CostRipEmd160(data)))
    }

    /**
     * Gas cost for sha256.
     */
    function CostRipEmd160(data: Array<u8>) : nat {
        // Determine number of words required to cover data.
        var d := (Int.RoundUp(|data|,32)/32);
        // Done
        600 + (120 * d)
    }

    // ========================================================================
    // (4) Identity
    // ========================================================================

    /**
     * The identify function just returns what it is given.
     */
    function CallID(data: Array<u8>) : Option<(Array<u8>,nat)> {
        Some((data, CostID(data)))
    }

    /**
     * Gas calculation for the identity function.
     */
    function CostID(data: Array<u8>) : nat {
        // Determine number of words required to cover data.
        var d := (Int.RoundUp(|data|,32)/32);
        // Done
        15 + (3 * d)
    }

    // ========================================================================
    // (5) ModExp
    // ========================================================================
    const G_QUADDIVISOR: nat := 3;

    /**
     * Compute arbitrary precision exponentiation under modulo.  Specifically,
     * we compue B^E % M.  All words are unsigned integers in big endian format.
     * See also EIP-2565.
     */
    function CallModExp(data: Array<u8>) : Option<(Array<u8>,nat)> {
        // Length of B
        var lB := Bytes.ReadUint256(data,0) as nat;
        // Length of E
        var lE := Bytes.ReadUint256(data,32) as nat;
        // Length of M
        var lM := Bytes.ReadUint256(data,64) as nat;
        // Extract B(ase)
        var B := Arrays.SliceAndPad(data,96,lB,0);
        // Extract E(xponent)
        var E := Arrays.SliceAndPad(data,96+lB,lE,0);
        // Extract M(odulo)
        var M := Arrays.SliceAndPad(data,96+lB+lE,lM,0);
        // Compute modexp
        var modexp := External.modExp(B,E,M);
        // Compute lEp
        var lEp := LenEp(lB,E,data);
        // Gas calculation
        var gascost := Int.Max(200, (f(Int.Max(lM,lB)) * Int.Max(lEp,1)) / G_QUADDIVISOR);
        // Done
        Some((modexp,gascost))
    }

    /**
     * Function "f" from the yellow paper.
     */
    function f(x: nat) : nat {
        var xd8 := Int.RoundUp(x,8) / 8;
        xd8 * xd8
    }

    /**
     * Calculation for "LenEp" (the Length of E primed) as stated in the yellow
     * paper.
     */
    function LenEp(lB: nat, E: Array<u8>, data: Array<u8>) : nat {
        var lE := |E|;
        //
        if lE <= 32 then
            // NOTE: the following could be improved by performing the log
            // directly on the byte sequence and, hence, avoiding the coercion.
            var w := Bytes.ReadUint256(Bytes.LeftPad(E,32),0);
            // Check where we stand
            if w == 0 then 0 else U256.Log2(w)
        else
            var w := Bytes.ReadUint256(data,96 + lB);
            var g := 8 * (lE - 32);
            // NOTE: the following could be improved by performing the log
            // directly on the byte sequence and, hence, avoiding the coercion.
            if 32 < lE && w != 0 then g + U256.Log2(w) else g
    }

    // ========================================================================
    // (6)
    // ========================================================================

    const G_BNADD := 150;

    function CallBnAdd(data: Array<u8>) : Option<(Array<u8>,nat)> {
        Some((data, G_BNADD))
    }

    // ========================================================================
    // (7)
    // ========================================================================

    const G_BNMUL := 6000;

    function CallBnMul(data: Array<u8>) : Option<(Array<u8>,nat)> {
        Some((data, G_BNMUL))
    }

    // ========================================================================
    // (8) Pairing
    // ========================================================================

    function CallSnarkV(data: Array<u8>) : Option<(seq<u8>,nat)> {
        Some((data, CostSnarkV(data)))
    }

    function CostSnarkV(data: Array<u8>) : nat {
        ((34000 * |data|) / 192) + 45000
    }

    // ========================================================================
    // (9) Blake2f
    // ========================================================================

    function CallBlake2f(data: Array<u8>) : Option<(Array<u8>,nat)> {
        if |data| == 213 && data[212] in {0,1}
        then
            var r := U32.Read(data,0) as nat;
            // FIXME: pull out stuff!
            Some((External.blake2f(data),r))
        else
            None
    }
}
