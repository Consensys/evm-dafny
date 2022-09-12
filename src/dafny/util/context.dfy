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
    // Block Context
    // =============================================================================
    datatype Block = Info(
        // Current block's beneficiary address.
        coinBase: u256,
        // Current block's timestamp.
        timeStamp: u256,
        // Current block's number.
        number: u256,
        // Current block's difficulty.
        difficulty: u256,
        // Current block's gas limit.
        gasLimit: u256,
        // Current chain ID.
        chainID: u256
    )

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
        // Return data from last contract call.
        returnData: seq<u8>,
        // Price of gas in current environment.
        gasPrice: u256,
        // Block information in current environment.
        block: Block
    ) {
        /**
         * Determine the size (in bytes) of the call data associated with this
         * context.
         */
        function method CallDataSize() : u256
        requires |this.callData| < TWO_256  {
            |this.callData| as u256
        }

        /**
         * Read a word from the call data associated with this context.
         */
        function method CallDataRead(loc: u256) : u256 {
            Bytes.ReadUint256(this.callData,loc as nat)
        }

        /**
         * Slice a sequence of bytes from the call data associated with this
         * context.
         */
        function method CallDataSlice(loc: u256, len: nat) : (data:seq<u8>)
        ensures |data| == len {
            Bytes.Slice(this.callData,loc as nat, len)
        }

        /**
         * Determine the size (in bytes) of the return data from the previous call
         * associated with this context.
         */
        function method ReturnDataSize() : nat
        requires |this.returnData| <= MAX_U256 {
            |this.returnData|
        }

        /**
         * Slice a sequence of bytes from the return data from the previous call
         * associated with this context.
         */
        function method ReturnDataSlice(loc: nat, len: nat) : (data:seq<u8>)
        // Return data cannot overflow.
        requires (loc + len) <= |this.returnData|
        ensures |data| == len {
            Bytes.Slice(this.returnData,loc, len)
        }

        /**
         * Update the return data associated with this state.
         */
        function method SetReturnData(data: seq<u8>) : Raw
        requires |data| <= MAX_U256 {
           this.(returnData:=data)
        }

    }

    type T = c:Raw | |c.callData| <= MAX_U256 && |c.returnData| <= MAX_U256
    witness Context(0,0,0,0,[],[],0,Info(0,0,0,0,0,0))

    /**
     * Create an initial context from various components.
     */
    function method Create(sender:u160,origin:u160,recipient:u160,callValue:u256,callData:seq<u8>,gasPrice:u256, block: Block) : T
    requires |callData| <= MAX_U256 {
        Context(sender,origin,address:=recipient,callValue:=callValue,callData:=callData,returnData:=[],gasPrice:=gasPrice,block:=block)
    }
}
