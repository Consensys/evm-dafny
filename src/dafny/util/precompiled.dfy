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
include "extern.dfy"

/**
 * Interface for the so-called "precompiled contracts".
 */
module Precompiled {
    import opened Int
    import U256
    import External

    function method Call(address: u160, data: seq<u8>) : seq<u8>
    requires address >= 1 && address <= 9 {
        match address
        case 1 => CallEcdsaRecover(data)
        case 2 => CallSha256(data)
        case 3 => CallRipEmd160(data)
        case 4 => CallID(data)
        case _ => [] // for now
    }

    function method Cost(address: u160, dataSize: nat) : nat
    requires address >= 1 && address <= 9 {
        match address
        case 1 => CostEcdsaRecover(dataSize)
        case 2 => CostSha256(dataSize)
        case 3 => CostRipEmd160(dataSize)
        case 4 => CostID(dataSize)
        case _ => 0 // for now
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
    function method CostEcdsaRecover(dataSize: nat) : nat {
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
    function method CostSha256(dataSize: nat) : nat {
        // Determine number of words required to cover data.
        var d := (Int.RoundUp(dataSize,32)/32);
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
    function method CostRipEmd160(dataSize: nat) : nat {
        // Determine number of words required to cover data.
        var d := (Int.RoundUp(dataSize,32)/32);
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
    function method CostID(dataSize: nat) : nat {
        // Determine number of words required to cover data.
        var d := (Int.RoundUp(dataSize,32)/32);
        // Done
        15 + (3 * d)
    }

    // ========================================================================
    // (5) ModExp
    // ========================================================================

    /**
     * The identify function just returns what it is given.
     */
    function method CallModExp(data: seq<u8>) : seq<u8> {
        data
    }

    /**
     * Gas calculation for the identity function.
     */
    function method CostModExp(dataSize: nat) : nat {
        200 // TODO
    }
}
