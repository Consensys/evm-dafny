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
include "extern.dfy"

/**
 * World state provides a snapshot of all accounts on the blockchain at a given
 * moment in time.
 */
module WorldState {
    import opened Int
    import Code
    import opened ExtraTypes
    import Storage
    import External

    /**
     * Account state associated with a given contract address.
     */
    datatype Account = Account(nonce:nat, balance: u256, storage: Storage.T, code: Code.T, hash: u256)

    /**
     * Create a new account.  This automatically constructs the appropriate code hash.
     */
    function method CreateAccount(nonce:nat, balance: u256, storage: Storage.T, code: Code.T) : Account {
        // Generate code hash
        var hash := External.sha3(code.contents);
        // Done
        Account(nonce,balance,storage,code,hash)
    }

    /**
     * Create a default account.  This has zero balance, empty storage and no code.
     */
    function method DefaultAccount() : Account {
        CreateAccount(0,0,Storage.Create(map[]),Code.Create([]))
    }

    /**
     * A mapping from contract addresses to accounts.
     */
    datatype T = WorldState(accounts:map<u160,Account>, modified:set<(u160,u256)>) {
        /**
         * Determine whether or not a given account exists.
         */
        function method Exists(account:u160) : bool {
            account in accounts
        }

        /**
         * Determine whether or not a given contract account can be created.
           The rules here say that, in some cases, when an account already
           exists at that address then you cannot overwrite it.
         */
        function method CanOverwrite(account:u160) : bool
        requires account in accounts {
            var data := accounts[account];
            |data.code.contents| == 0 && data.nonce == 0
        }


        /**
         * Determine whether or not a given acount is an end-user account.
         */
        function method isEndUser(account:u160) : bool
        requires account in accounts {
            Code.Size(accounts[account].code) == 0
        }

        /**
         * Determine whether or not an account is considered to be "empty".
         */
        function method IsEmpty(account:u160) : bool
        requires account in accounts {
            var data := accounts[account];
            Code.Size(data.code) == 0 && data.nonce == 0 && data.balance == 0
        }

        /**
         * An account is dead when its account state is non-existent or empty.
         */
        function method IsDead(account:u160) : bool {
            !(account in accounts) || IsEmpty(account)
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
         * exists, a default (i.e. empty) account is returned.
         */
        function method GetOrDefault(account:u160) : Account {
            if account in accounts
            then
                accounts[account]
            else
                DefaultAccount()
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
         * Check whether we can deposit without causing an overflow.
         */
        function method CanDeposit(account:u160, value: u256) : bool
        // Account must be valid!
        requires account in this.accounts {
            (MAX_U256 as u256 - accounts[account].balance) >= value
        }

        /**
         * Check whether we can withdraw without causing an underflow.
         */
        function method CanWithdraw(account:u160, value: u256) : bool
        // Account must be valid!
        requires account in this.accounts {
            accounts[account].balance >= value
        }

        /**
         * Withdraw a given amount of Wei into this account.
         */
        function method Withdraw(account:u160, value: u256) : T
        // Account must be valid!
        requires account in this.accounts
        // Ensure balance does not overflow!
        requires CanWithdraw(account,value) {
            // Extract account data
            var entry := accounts[account];
            // Compute updated balance.
            var nBalance := entry.balance - value;
            // Write it back
            this.(accounts:=this.accounts[account:=entry.(balance:=nBalance)])
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
         * Transfer a given amount of Wei from one account to another.
         */
        function method Transfer(from:u160, to: u160, value: u256) : T
        // Both accounts must be valid
        requires from in this.accounts && to in this.accounts
        // Ensure balance does not overflow!
        requires CanWithdraw(from,value) && CanDeposit(to,value) {
            // Transfer funds
            this.Withdraw(from,value).Deposit(to,value)
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
            // Generate code hash
            var hash := External.sha3(code);
            // Write it back
            this.(accounts:=this.accounts[account:=entry.(code:=Code.Create(code),hash:=hash)])
        }

        /**
         * Increment the nonce associated with a given account.
         */
        function method IncNonce(account:u160) : T
        // Account must be valid!
        requires account in this.accounts {
            // Extract account data
            var entry := accounts[account];
            // Increment the nonce
            this.(accounts:=this.accounts[account:=entry.(nonce:=entry.nonce+1)])
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
            // Update modification record (if applicable).
            var nmodified := if value != pValue then modified + {(account,address)} else modified;
            // Write it all back
            WorldState(this.accounts[account:=entry.(storage:=nStorage)],nmodified)
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
        WorldState(accounts, {})
    }
}
