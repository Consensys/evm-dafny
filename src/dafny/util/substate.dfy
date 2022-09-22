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
    datatype T = SubState(
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
        refund: nat,
        // The set of accessed account addresses.
        accessedAccounts:set<u160>,
        // The set of accessed storage keys.
        accessedKeys:set<(u160,u256)>)
    {
        /**
         * Append zero or more entries onto the current log.
         */
        function method Append(entries: seq<LogEntry>) : T {
            this.(log := this.log + entries)
        }

        /**
         * Register an account for self destruction.
         */
        function method AccountDestructed(account: u160) : T {
            this.(selfDestruct := this.selfDestruct + {account})
        }

        /**
         * Check whether a given account was previously accessed or not.
         */
        function method WasAccountAccessed(account: u160) : bool {
            account in accessedAccounts
        }

        /**
         * Mark a particular account as having been "accessed".
         */
        function method AccountAccessed(account: u160) : T {
            var naccessed := accessedAccounts + {account};
            this.(accessedAccounts := naccessed)
        }

        /**
         * Check whether a given storage location was previously accessed or not.
         */
        function method WasKeyAccessed(account: u160, address: u256) : bool {
            (account,address) in accessedKeys
        }

        /**
         * Mark a particular storage location as having been "accessed".
         */
        function method KeyAccessed(account: u160, address: u256) : T {
            var naccessed := accessedKeys + {(account,address)};
            this.(accessedKeys := naccessed)
        }

    }

    /**
     * Create an initially empty substate.  This is "A_0" in the yellow paper.
     */
    function method Create() : T {
        SubState({},[],{},0,{},{})
    }
}
