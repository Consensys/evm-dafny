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
include "code.dfy"
include "storage.dfy"
include "../util/int.dfy"
include "../util/extern.dfy"

/**
 * World state provides a snapshot of all accounts on the blockchain at a given
 * moment in time.
 */
module WorldState {
    import opened Int
    import Code
    import opened Optional
    import Storage
    import External

    // Sha3 hash of the empty sequence.
    const HASH_EMPTYCODE : u256 := 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    /**
     * Account state associated with a given contract address.
     */
    datatype Account = Account(nonce:nat, balance: u256, storage: Storage.T, code: Code.T, hash: u256)

    /**
     * Create a new account.  This automatically constructs the appropriate code hash.
     */
    function CreateAccount(nonce:nat, balance: u256, storage: Storage.T, code: Code.T, hash: u256) : Account {
        Account(nonce,balance,storage,code,hash)
    }

    /**
     * Create a default account.  This has zero balance, empty storage and no code.
     */
    function DefaultAccount() : Account {
        CreateAccount(0,0,Storage.Create(map[]),Code.Create([]),HASH_EMPTYCODE)
    }

    /**
     * A mapping from contract addresses to accounts.
     */
    datatype T = WorldState(accounts:map<u160,Account>, pretransactionaccounts:map<u160,Account>) {
        /**
         * Determine whether or not a given account exists.
         */
        function Exists(account:u160) : bool {
            account in accounts
        }

        /**
         * Determine whether or not a given contract account can be created.
           The rules here say that, in some cases, when an account already
           exists at that address then you cannot overwrite it.
         */
        function CanOverwrite(account:u160) : bool
        requires account in accounts {
            var data := accounts[account];
            |data.code.contents| == 0 && data.nonce == 0
        }


        /**
         * Determine whether or not a given acount is an end-user account.
         */
        function isEndUser(account:u160) : bool
        requires account in accounts {
            Code.Size(accounts[account].code) == 0
        }

        /**
         * Determine whether or not an account is considered to be "empty".
         */
        function IsEmpty(account:u160) : bool
        requires account in accounts {
            var data := accounts[account];
            Code.Size(data.code) == 0 && data.nonce == 0 && data.balance == 0
        }

        /**
         * An account is dead when its account state is non-existent or empty.
         */
        function IsDead(account:u160) : bool {
            !(account in accounts) || IsEmpty(account)
        }

        /**
         * Get the account associated with a given address.  If no such account
         * exists, none is returned.
         */
        function GetAccount(account:u160) : Option<Account> {
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
        function GetOrDefault(account:u160) : Account {
            if account in accounts
            then
                accounts[account]
            else
                DefaultAccount()
        }

        /**
         * Get the account associated with a given address in the world state prior to the transaction execution.  If no such account
         * exists, a default (i.e. empty) account is returned.
         */
        function GetOrDefaultPretransaction(account:u160) : Account {
            if account in pretransactionaccounts
            then
                pretransactionaccounts[account]
            else
                DefaultAccount()
        }

        /**
         * Put a given account into the world state at a given address.
         */
        function Put(account:u160, data: Account) : T {
            this.(accounts:=this.accounts[account:=data])
        }

        /**
         * Ensure an account exists at a given address in the world state.  If
           it doesn't, then a default one is created.
         */
        function EnsureAccount(address: u160) :T {
            if Exists(address) then this
            else
                // Configure default account
                Put(address,DefaultAccount())
        }

        /**
         * Determine balance of a given account.
         */
        function Balance(account:u160) : u256
        // Account must be valid!
        requires account in this.accounts {
            accounts[account].balance
        }

        /**
         * Check whether we can deposit without causing an overflow.
         */
        function CanDeposit(account:u160, value: u256) : bool
        // Account must be valid!
        requires account in this.accounts {
            (MAX_U256 as u256 - accounts[account].balance) >= value
        }

        /**
         * Check whether we can withdraw without causing an underflow.
         */
        function CanWithdraw(account:u160, value: u256) : bool
        // Account must be valid!
        requires account in this.accounts {
            accounts[account].balance >= value
        }

        /**
         * Withdraw a given amount of Wei from this account.
         */
        function Withdraw(account:u160, value: u256) : T
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
        function Deposit(account:u160, value: u256) : T
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
        function Transfer(from:u160, to: u160, value: u256) : T
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
        function SetCode(account:u160, code: seq<u8>, hash: u256) : T
        // Account must be valid!
        requires account in this.accounts
        // Code must be valid size.
        requires |code| <= Code.MAX_CODE_SIZE {
            // Extract account data
            var entry := accounts[account];
            // Write it back
            this.(accounts:=this.accounts[account:=entry.(code:=Code.Create(code),hash:=hash)])
        }

        /**
         * Get the current nonce value for an account.  The account must exist.
         */
        function Nonce(account:u160) : nat
        // Account must be valid!
        requires account in this.accounts {
            accounts[account].nonce
        }

        /**
         * Increment the nonce associated with a given account.
         */
        function IncNonce(account:u160) : T
        // Account must be valid!
        requires account in this.accounts
        // Ensure the nonce cannot overflow
        requires Nonce(account) < MAX_U64 {
            // Extract account data
            var entry := accounts[account];
            // Increment the nonce
            this.(accounts:=this.accounts[account:=entry.(nonce:=entry.nonce+1)])
        }

        /**
         * Write into the storage of a given account.
         */
        function Write(account:u160, address: u256, value: u256) : T
        // Account must be valid!
        requires account in this.accounts {
            // Extract account data
            var entry := accounts[account];
            // Extract previous value
            var pValue := Storage.Read(entry.storage,address);
            // Update account storage
            var nStorage := Storage.Write(entry.storage,address,value);
            // Write it all back
            WorldState(this.accounts[account:=entry.(storage:=nStorage)],pretransactionaccounts)
        }

        /**
         * Read a value from the storage of a given account.
         */
        function Read(account:u160, address: u256) : u256
        // Account must be valid!
        requires account in this.accounts {
            // Extract account data
            var entry := accounts[account];
            // Read from account storage
            Storage.Read(entry.storage,address)
        }
    }

    /**
     * Create world state from an initial mapping of addresses to accounts, and thread through a copy of the pre-transaction world.
     */
    function Create(accounts:map<u160,Account>) : T {
        // Initially all accessed / modified flags are cleared.
        WorldState(accounts, accounts)
    }
}
