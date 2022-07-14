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
    // Address of currently executing account.
    address: u160,
    // Address of sender of original transaction.
    origin: u160,
    // Address of account responsible for this execution.
    caller: u160,
    // Input data associated with this call.
    calldata:seq<u8>
    )

    type T = c:Raw | |c.calldata| <= MAX_U256 witness Context(0,0,0,[])

    /**
     * Create an initial context from various components.
     */
    function method create(origin:u160,calldata:seq<u8>) : T
    requires |calldata| <= MAX_U256 {
        Context(address:=origin,origin:=origin,caller:=origin,calldata:=calldata)
    }

    /**
     * Determine the size (in bytes) of the call data associated with this context.
     */
    function method data_size(ctx: T) : u256 {
      |ctx.calldata| as u256
    }

    /**
     * Read a word from the call data associated with this context.
     */
    function method data_read(ctx: T, loc: u256) : u256 {
      Bytes.read_u256(ctx.calldata,loc as nat)
    }
}
