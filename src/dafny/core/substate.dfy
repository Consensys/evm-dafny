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
include "../util/int.dfy"

module SubState {
     import opened Int

    /**
     * A log entry consists of between zero and four topics, along with zero or
     * more bytes.
     */
    type LogEntry = l:(seq<u256>, seq<u8>) | |l.0| <= 4 witness ([],[])

    /**
     * A mapping from contract addresses to accounts.
     */
    datatype Raw = SubState(
        // The set of accounts that will be discarded following the
        // transaction's completion.
        selfDestruct: set<u160>,
        // The log series.  A series of archived and indexable "checkpoints" in
        // VM code execution that allow for contract-calls to be easily tracked
        // by onlookers.
        log: seq<LogEntry>,
        // The set of touched accounts, of which the empty ones are deleted at
        // the end of a transaction.
        touched: set<(u160,u256)>,
        // The refund balance which increased through SSTORE.
        refund: int,
        // The set of accessed account addresses.
        accessedAccounts:set<u160>,
        // The set of accessed storage keys.
        accessedKeys:set<(u160,u256)>)
    {
        /**
         * Append zero or more entries onto the current log.
         */
        function Append(entries: seq<LogEntry>) : Raw {
            this.(log := this.log + entries)
        }

        /**
         * Register an account for self destruction.
         */
        function AccountDestructed(account: u160) : Raw {
            this.(selfDestruct := this.selfDestruct + {account})
        }

        /**
         * Check whether a given account was previously accessed or not.
         */
        function WasAccountAccessed(account: u160) : bool {
            account in accessedAccounts
        }

        /**
         * Mark a particular account as having been "accessed".
         */
        function AccountAccessed(account: u160) : Raw {
            var naccessed := accessedAccounts + {account};
            this.(accessedAccounts := naccessed)
        }

        /**
         * Check whether a given storage location was previously accessed or not.
         */
        function WasKeyAccessed(account: u160, address: u256) : bool {
            (account,address) in accessedKeys
        }

        /**
         * Mark a particular storage location as having been "accessed".
         */
        function KeyAccessed(account: u160, address: u256) : Raw {
            var naccessed := accessedKeys + {(account,address)};
            this.(accessedKeys := naccessed)
        }

        function ModifyRefundCounter(k: int): Raw {
            this.(refund := this.refund + k)
        }

    }

    /**
     * Define the substate as the raw state with an additional invariant that
     * all precompiled contracts are always considered as having been accessed.
     */
    type T = c:Raw | {1,2,3,4,5,6,7,8,9} <= c.accessedAccounts
    witness SubState({},[],{},0,{1,2,3,4,5,6,7,8,9},{})

    /**
     * Create an initially empty substate.  This is "A_0" in the yellow paper.
     */
    function Create() : T {
        SubState({},[],{},0,{1,2,3,4,5,6,7,8,9},{})
    }
}
