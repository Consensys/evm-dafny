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

module Context {
  import opened Int

  // =============================================================================
  // Transaction Context
  // =============================================================================

  datatype T = Context(
    // Address of currently executing account.
    address: u160,
    // Address of sender of original transaction.
    origin: u160,
    // Address of account responsible for this execution.
    caller: u160,
    // Input data associated with this call.
    calldata:seq<u8>
    )
}
