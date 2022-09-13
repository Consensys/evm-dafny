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
include "code.dfy"
include "ExtraTypes.dfy"
include "storage.dfy"

/**
 * World state provides a snapshot of all accounts on the blockchain at a given
 * moment in time.
 */
module WorldState {
    import opened Int
    import Code
    import opened ExtraTypes
    import Storage

    /**
     * Account state associated with a given contract address.
     */
    datatype Account = Account(nonce:nat, balance: nat, storage: Storage.T, code: Code.T)

    /**
     * Create a default account.  This has zero balance, empty storage and no code.
     */
    function method DefaultAccount() : Account {
        Account(nonce:=0,balance:=0,storage:=Storage.Create(map[]),code:=Code.Create([]))
    }

    /**
     * A mapping from contract addresses to accounts.
     */
    datatype T = WorldState(accounts:map<u160,Account>) {
        /**
         * Determine whether or not a given account exists.
         */
        function method Exists(account:u160) : bool {
            account in accounts
        }

        /**
         * Determine whether or not a given acount is an end-user account.
         */
        function method isEndUser(account:u160) : bool
        requires account in accounts {
            Code.Size(accounts[account].code) == 0
        }

        /**
         * Get the account associated with a given address.  If no such account
         * exists, none is returned.
         */
        function method Get(account:u160) : Option<Account> {
            if account in accounts
            then
                Some(accounts[account])
            else
                None
        }

        /**
         * Get the account associated with a given address.  If no such account
         * exists, a default account is created.
         */
        function method GetOrCreate(account:u160) : (Account,T) {
            if account in accounts
            then
                (accounts[account],this)
            else
                var nAccount := DefaultAccount();
                (nAccount,this.Put(account,nAccount))
        }

        /**
         * Put a given account into the world state at a given address.
         */
        function method Put(account:u160, data: Account) : T {
            WorldState(this.accounts[account:=data])
        }

        /**
         * Deposit a given amount of Wei into this account.
         */
        function method Deposit(account:u160, value: nat) : T
        // Account must be valid!
        requires account in this.accounts {
            // Extract account data
            var entry := accounts[account];
            // Compute updated balance.
            var nBalance := entry.balance + value;
            // Write it back
            WorldState(this.accounts[account:=entry.(balance:=nBalance)])
        }

        /**
         * Write into the storage of a given account.
         */
        function method Write(account:u160, address: u256, value: u256) : T
        // Account must be valid!
        requires account in this.accounts {
            // Extract account data
            var entry := accounts[account];
            // Update account storage
            var nStorage := Storage.Write(entry.storage,address,value);
            // Write it back
            WorldState(this.accounts[account:=entry.(storage:=nStorage)])
        }

        /**
         * Read a value from the storage of a given account.
         */
        function method Read(account:u160, address: u256) : u256
        // Account must be valid!
        requires account in this.accounts {
            // Extract account data
            var entry := accounts[account];
            // Read from account storage
            Storage.Read(entry.storage,address)
        }
    }

    /**
     * Create world state from an initial mapping of addresses to accounts.
     */
    function method Create(accounts:map<u160,Account>) : T {
        WorldState(accounts)
    }
}
