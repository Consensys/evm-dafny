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
include "bytes.dfy"
include "extern.dfy"
include "int.dfy"
include "ExtraTypes.dfy"

/**
 * Interface for the so-called "precompiled contracts".
 */
module Precompiled {
    import opened Int
    import opened ExtraTypes
    import U32
    import U256
    import External
    import Bytes

    function method Call(address: u160, data: seq<u8>) : Option<(seq<u8>,nat)>
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
     * Key recovery.
     */
    function method CallEcdsaRecover(data: seq<u8>) : Option<(seq<u8>,nat)> {
        Some((data, G_ECDSA))
    }

    // ========================================================================
    // (2) SHA256
    // ========================================================================

    /**
     * SHA256
     */
    function method CallSha256(data: seq<u8>) : Option<(seq<u8>,nat)> {
        Some((External.sha256(data),CostSha256(data)))
    }

    /**
     * Gas cost for sha256.
     */
    function method CostSha256(data: seq<u8>) : nat {
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
    function method CallRipEmd160(data: seq<u8>) : Option<(seq<u8>,nat)> {
        Some((External.ripEmd160(data), CostRipEmd160(data)))
    }

    /**
     * Gas cost for sha256.
     */
    function method CostRipEmd160(data: seq<u8>) : nat {
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
    function method CallID(data: seq<u8>) : Option<(seq<u8>,nat)> {
        Some((data, CostID(data)))
    }

    /**
     * Gas calculation for the identity function.
     */
    function method CostID(data: seq<u8>) : nat {
        // Determine number of words required to cover data.
        var d := (Int.RoundUp(|data|,32)/32);
        // Done
        15 + (3 * d)
    }

    // ========================================================================
    // (5) ModExp
    // ========================================================================
    const G_QUADDIVISOR: nat := 100;

    /**
     * Compute arbitrary precision exponentiation under modulo.  Specifically,
     * we compue B^E % M.  All words are unsigned integers in big endian format.
     */
    function method CallModExp(data: seq<u8>) : Option<(seq<u8>,nat)> {
        // Length of B
        var lB := Bytes.ReadUint256(data,0) as nat;
        // Length of E
        var lE := Bytes.ReadUint256(data,32) as nat;
        // Length of M
        var lM := Bytes.ReadUint256(data,64) as nat;
        // Extract B(ase)
        var B := Bytes.Slice(data,96,lB);
        // Extract E(xponent)
        var E := Bytes.Slice(data,96+lB,lE);
        // Extract M(odulo)
        var M := Bytes.Slice(data,96+lB+lE,lM);
        // Compute modexp (+lEp)
        var (modexp,lEp) := External.modExp(B,E,M);
        // Gas calculation
        var gascost := Int.Max(200,f(Int.Max(lM,lB)) * Int.Max(lEp,1) / G_QUADDIVISOR);
        // Done
        Some((modexp,gascost))
    }

    function method f(x: nat) : nat {
        var xd8 := Int.RoundUp(x,8) / 8;
        x * x
    }

    // ========================================================================
    // (6)
    // ========================================================================

    const G_BNADD := 150;

    function method CallBnAdd(data: seq<u8>) : Option<(seq<u8>,nat)> {
        Some((data, G_BNADD))
    }

    // ========================================================================
    // (7)
    // ========================================================================

    const G_BNMUL := 6000;

    function method CallBnMul(data: seq<u8>) : Option<(seq<u8>,nat)> {
        Some((data, G_BNMUL))
    }

    // ========================================================================
    // (8) Pairing
    // ========================================================================

    function method CallSnarkV(data: seq<u8>) : Option<(seq<u8>,nat)> {
        Some((data, CostSnarkV(data)))
    }

    function method CostSnarkV(data: seq<u8>) : nat {
        ((34000 * |data|) / 192) + 45000
    }

    // ========================================================================
    // (9) Blake2f
    // ========================================================================

    function method CallBlake2f(data: seq<u8>) : Option<(seq<u8>,nat)> {
        if |data| == 213 && data[212] in {0,1}
        then
            var r := U32.Read(data,0) as nat;
            // FIXME: pull out stuff!
            Some((External.blake2f(data),r))
        else
            None
    }
}
