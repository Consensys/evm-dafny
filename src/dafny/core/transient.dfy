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
include "storage.dfy"

/**
 * Storage on the EVM which is associated with a particular contract address.
 */
module TransientStorage {
  import opened Int
  import Storage

  datatype T = TransientStorage(contents:map<u160,Storage.T>) {
   /**
    * Write into the transient storage of a given account.
    */
    function Write(account:u160, address: u256, value: u256) : T {
      // Extract account data          
      var entry := if account in this.contents
      then
        // Transient storage already exists for this account
        this.contents[account]
      else 
        // Fresh transient storage.
        Storage.Create(map[]);
        // Update account storage
      var nStorage := Storage.Write(entry,address,value);
      // Write it all back
      TransientStorage(this.contents[account:=nStorage])
    }

   /**
    * Read a value from the transient storage of a given account.
    */
    function Read(account:u160, address: u256) : u256
    {
      if account in this.contents
      then
        // Extract account data
        var entry := this.contents[account];
        // Read from account storage
        Storage.Read(entry,address)
      else
        0
    }
  }

  /**
   * Default empty storage
   */
  function Create() : T {
    TransientStorage(map[])
  }
}