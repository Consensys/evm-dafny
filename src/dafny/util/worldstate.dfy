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
    datatype Account = Account(nonce:nat, balance: u256, storage: Storage.T, code: Code.T)

    /**
     * Create a default account.  This has zero balance, empty storage and no code.
     */
    function method DefaultAccount() : Account {
        Account(nonce:=0,balance:=0,storage:=Storage.Create(map[]),code:=Code.Create([]))
    }

    /**
     * A mapping from contract addresses to accounts.
     */
    datatype T = WorldState(accounts:map<u160,Account>, accessed:set<(u160,u256)>, modified:set<(u160,u256)>) {
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
            this.(accounts:=this.accounts[account:=data])
        }

        /**
         * Ensure an account exists at a given address in the world state.  If
           it doesn't, then a default one is created.
         */
        function method EnsureAccount(address: u160) :T {
            if Exists(address) then this
            else
                // Configure default account
                Put(address,DefaultAccount())
        }

        /**
         * Determine balance of a given account.
         */
        function method Balance(account:u160) : u256
        // Account must be valid!
        requires account in this.accounts {
            accounts[account].balance
        }

        /**
         * Check whether we can deposity without causing an overflow.
         */
        function method CanDeposit(account:u160, value: u256) : bool
        // Account must be valid!
        requires account in this.accounts {
            (MAX_U256 as u256 - accounts[account].balance) >= value
        }

        /**
         * Deposit a given amount of Wei into this account.
         */
        function method Deposit(account:u160, value: u256) : T
        // Account must be valid!
        requires account in this.accounts
        // Ensure balance does not overflow!
        requires CanDeposit(account,value) {
            // Extract account data
            var entry := accounts[account];
            // Compute updated balance.
            var nBalance := entry.balance + value;
            // Write it back
            this.(accounts:=this.accounts[account:=entry.(balance:=nBalance)])
        }

        /**
         * Set the code associated with a given contract account.
         */
        function method SetCode(account:u160, code: seq<u8>) : T
        // Account must be valid!
        requires account in this.accounts
        // Code must be valid size.
        requires |code| <= Code.MAX_CODE_SIZE {
            // Extract account data
            var entry := accounts[account];
            // Write it back
            this.(accounts:=this.accounts[account:=entry.(code:=Code.Create(code))])
        }

        /**
         * Write into the storage of a given account.
         */
        function method Write(account:u160, address: u256, value: u256) : T
        // Account must be valid!
        requires account in this.accounts {
            // Extract account data
            var entry := accounts[account];
            // Extract previous value
            var pValue := Storage.Read(entry.storage,address);
            // Update account storage
            var nStorage := Storage.Write(entry.storage,address,value);
            // Update access record
            var naccessed := accessed + {(account,address)};
            // Update modification record (if applicable).
            var nmodified := if value != pValue then modified + {(account,address)} else modified;
            // Write it all back
            WorldState(this.accounts[account:=entry.(storage:=nStorage)],naccessed,nmodified)
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

        /**
         * Check whether a given storage location was previously accessed or not.
         */
        function method WasAccessed(account: u160, address: u256) : bool {
            (account,address) in accessed
        }

        /**
         * Mark a particular storage location as having been "accessed".
         */
        function method Accessed(account: u160, address: u256) : T {
            var naccessed := accessed + {(account,address)};
            this.(accessed := naccessed)
        }

        /**
         * Check whether a given storage location was previously modified or not.
         */
        function method WasModified(account: u160, address: u256) : bool {
            (account,address) in modified
        }

        /**
         * Mark a particular storage location as having been "modified".
         */
        function method Modified(account: u160, address: u256) : T {
            var nmodified := modified + {(account,address)};
            this.(modified := nmodified)
        }
    }

    /**
     * Create world state from an initial mapping of addresses to accounts.
     */
    function method Create(accounts:map<u160,Account>) : T {
        // Initially all accessed / modified flags are cleared.
        WorldState(accounts, {}, {})
    }
}
