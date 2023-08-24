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

include "../../../dafny/evm.dfy"
include "../utils.dfy"

module ForkTests {
    import opened Int
    import opened Bytecode
    import opened EVM
    import opened EvmState
    import opened Opcode
    import Stack
    import opened Utils

    method {:test} berlin_01()
    {
        var vm := EVM.Init(0, EvmFork.BERLIN, code:=[BASEFEE]);
        EvmFork.BerlinFacts();
        AssertAndExpect(BASEFEE !in EvmFork.BERLIN_BYTECODES);
        vm := EVM.Execute(vm);
        assert vm == ERROR(INVALID_OPCODE);
    }

    method {:test} london_01()
    {
        var vm := EVM.Init(0, EvmFork.LONDON, code:=[BASEFEE]);
        EvmFork.LondonFacts();
        AssertAndExpect(BASEFEE in EvmFork.LONDON_BYTECODES);
        vm := EVM.Execute(vm);
        assert vm != ERROR(INVALID_OPCODE);
    }
}
