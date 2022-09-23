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

/**
 * Interface for the so-called "precompiled contracts".
 */
module Precompiled {
    import opened Int
    import U256
    import External
    import Bytes

    function method Call(address: u160, data: seq<u8>) : seq<u8>
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

    function method Cost(address: u160, data: seq<u8>) : nat
    requires address >= 1 && address <= 9 {
        match address
        case 1 => CostEcdsaRecover(data)
        case 2 => CostSha256(data)
        case 3 => CostRipEmd160(data)
        case 4 => CostID(data)
        case 5 => CostModExp(data)
        case 6 => CostBnAdd(data)
        case 7 => CostBnMul(data)
        case 8 => CostSnarkV(data)
        case 9 => CostBlake2f(data)
    }

    // ========================================================================
    // (1) ECDSA Recover
    // ========================================================================

    /**
     * Key recovery.
     */
    function method CallEcdsaRecover(data: seq<u8>) : seq<u8> {
        data
    }

    /**
     * Gas cost for key recovery.
     */
    function method CostEcdsaRecover(data: seq<u8>) : nat {
        3000
    }

    // ========================================================================
    // (2) SHA256
    // ========================================================================

    /**
     * SHA256
     */
    function method CallSha256(data: seq<u8>) : seq<u8> {
        External.sha256(data)
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
    function method CallRipEmd160(data: seq<u8>) : seq<u8> {
        data
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
    function method CallID(data: seq<u8>) : seq<u8> {
        data
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
     * The identify function just returns what it is given.
     */
    function method CallModExp(data: seq<u8>) : seq<u8> {
        data
    }

    /**
     * Gas calculation for the identity function.
     */
    function method CostModExp(data: seq<u8>) : nat {
        var Lb := Bytes.ReadUint32(data,0) as nat;
        var Le := Bytes.ReadUint32(data,4) as nat;
        var Lm := Bytes.ReadUint32(data,8) as nat;
        var r := f(Int.Max(Lm,Lb)) * Int.Max(Le,1) / G_QUADDIVISOR;
        Int.Max(200,r)
    }

    function method f(x: nat) : nat {
        var xd8 := Int.RoundUp(x,8) / 8;
        x * x
    }

    // ========================================================================
    // (6)
    // ========================================================================

    function method CallBnAdd(data: seq<u8>) : seq<u8> {
        data
    }

    function method CostBnAdd(data: seq<u8>) : nat {
        150
    }

    // ========================================================================
    // (7)
    // ========================================================================

    function method CallBnMul(data: seq<u8>) : seq<u8> {
        data
    }

    function method CostBnMul(data: seq<u8>) : nat {
        6000
    }

    // ========================================================================
    // (8) Pairing
    // ========================================================================

    function method CallSnarkV(data: seq<u8>) : seq<u8> {
        data
    }

    function method CostSnarkV(data: seq<u8>) : nat {
        ((34000 * |data|) / 192) + 45000
    }

    // ========================================================================
    // (9) Blake2f
    // ========================================================================

    function method CallBlake2f(data: seq<u8>) : seq<u8> {
        data
    }

    function method CostBlake2f(data: seq<u8>) : nat {

        200 // TODO
    }
}
