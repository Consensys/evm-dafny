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
include "state.dfy"

/**
 * Top-level definition of an Ethereum Virtual Machine.
 */
abstract module EVM {
    import opened EvmState

    function method Execute(st:State) : State
    // To execute a bytecode requires the machine is in a non-terminal state.
    requires !st.IsFailure()
}
