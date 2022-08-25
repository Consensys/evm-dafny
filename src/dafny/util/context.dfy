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
include "bytes.dfy"

module Context {
  import opened Int
  import Bytes

  // =============================================================================
  // Transaction Context
  // =============================================================================

  datatype Raw = Context(
    // Address of account responsible for this execution.
    sender: u160,
    // Address of original transaction.
    origin: u160,
    // Address of currently executing account.
    address: u160,
    // Value deposited by instruction / transaction responsible for this execution.
    callValue: u256,
    // Input data associated with this call.
    callData:seq<u8>,
    // Price of gas in current environment.
    gasPrice: u256
    )

    type T = c:Raw | |c.callData| <= MAX_U256 witness Context(0,0,0,0,[],0)

    /**
     * Create an initial context from various components.
     */
    function method Create(sender:u160,origin:u160,recipient:u160,callValue:u256,callData:seq<u8>,gasPrice:u256) : T
    requires |callData| <= MAX_U256 {
        Context(sender,origin,address:=recipient,callValue:=callValue,callData:=callData,gasPrice:=gasPrice)
    }

    /**
     * Determine the size (in bytes) of the call data associated with this context.
     */
    function method DataSize(ctx: T) : u256 {
      |ctx.callData| as u256
    }

    /**
     * Read a word from the call data associated with this context.
     */
    function method DataRead(ctx: T, loc: u256) : u256 {
      Bytes.ReadUint256(ctx.callData,loc as nat)
    }

    /**
     * Slice a sequence of bytes from the call data associated with this context.
     */
    function method DataSlice(ctx: T, loc: u256, len: nat) : seq<u8> 
      ensures |DataSlice(ctx, loc, len)| == len 
    {
      Bytes.Slice(ctx.callData,loc as nat, len)
    }
}
