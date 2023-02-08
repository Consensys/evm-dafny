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

include "../../../dafny/evms/berlin.dfy"

/** Provide some tests to check some qualitative properties of bytecode.
 *
 *  We use an EVM with no gas as the bytecode high-level instructions
 *  like `Push1` do not consume gas.
 */
module Optimisations {

    import opened Int
    import opened Bytecode
    import opened EvmBerlin
    import opened EvmState
    import opened Opcode
    import Stack

    //  Some optimisation examples from
    // https://fenix.tecnico.ulisboa.pt/cursos/mma/dissertacao/1691203502343808

    /**
     *  Proposition 12: n + 1 consecutive Pop  <_gas SwapN n + 1 consecutive Pop
     *  Gas cost for POP is G_BASE and for SWAP G_VERYLOW
     *
     *  @param  s   An initial stack content.
     *  @param  g   An initial value of gas.
     *
     *  @note   Case n = 1
     */
    method Proposition12a(s: seq<u256>, g: nat)
        /** Stack must have at least 2 elements. */
        requires 2 <= |s| <= 1024
        /** Minimum gas needed. */
        requires g >= 2 * Gas.G_BASE + Gas.G_VERYLOW
    {
        var vm := EvmBerlin.Init(gas := g, stk := s, code := []);
        //  execute 2 POPs
        var vm1 := vm;
        vm1 := ExecuteOP(vm1, POP);
        vm1 := ExecuteOP(vm1, POP);

        //  execute SWAP1 and 2 POPs
        var vm2 := vm;
        vm2 := ExecuteOP(vm2, SWAP1);
        vm2 := ExecuteOP(vm2, POP);
        vm2 := ExecuteOP(vm2, POP);

        //  States are the same except for gas and PC
        assert vm1.evm.(pc := 0, gas := 0) == vm2.evm.(pc := 0, gas :=0);
        //  Gas saved is Gas.G_VERYLOW
        assert vm2.Gas() == vm1.Gas() - Gas.G_VERYLOW;
        assert vm2.Gas() < vm1.Gas();
    }

    /**
     *
     *  Proposition 12: n + 1 consecutive Pop  <_gas SwapN n + 1 consecutive Pop
     *  Gas cost for POP is G_BASE and for SWAP G_VERYLOW
     *
     *  @param  n   As described above.
     *  @param  s   An initial stack content.
     *  @param  g   An initial value of gas.
     *
     *  @note       General case.
     *
     */
    method Proposition12b(n: nat, s: seq<u256>, g: nat)
        requires 1 <= n <= 16
        /** Stack must have at least n + 1 elements. */
        requires n + 1 <= |s| <= 1024
        /** Minimum gas needed. */
        requires g >= (n + 1) * Gas.G_BASE + Gas.G_VERYLOW
    {
        var vm := EvmBerlin.Init(gas := g, stk := s, code := []);

        //  Execute n + 1 POPs in vm1.
        var vm1 := vm;
        for i := 0 to n + 1
            invariant vm1.EXECUTING?
            invariant vm1.Gas() == g - (i * Gas.G_BASE)
            invariant vm1.Operands() >= n - i
            invariant vm1.GetStack() == vm.SlicePeek(i, |s|)
        {
            vm1 := ExecuteOP(vm1, POP);
            assert vm1.EXECUTING?;
        }
        assert vm1.Gas() >= Gas.G_VERYLOW;
        assert vm1.Gas() == g - ((n+1) * Gas.G_BASE);
        //  Stack after n + 1 POPs is suffix of initial stack starting at index n + 1
        assert vm1.GetStack() == vm.SlicePeek(n + 1, |s|);

        //  Execute SWAPn and then n POPs in vm2.
        var vm2 := vm;
        vm2 := Swap(vm2, n).UseGas(Gas.G_VERYLOW);

        for i := 0 to n + 1
        invariant vm2.EXECUTING?
        invariant vm2.Gas() == g - (i * Gas.G_BASE)  - Gas.G_VERYLOW
        invariant vm2.Operands() >= n + 1 - i
        invariant vm2.Operands() == vm.Operands() - i == |s| - i
        invariant vm2.SlicePeek(n + 1 - i, |s| - i) == vm.SlicePeek(n + 1, |s|)
        {
            vm2 := ExecuteOP(vm2, POP);
            assert vm2.EXECUTING?;
        }
        assert vm2.SlicePeek(0, |s| - n - 1) == vm.SlicePeek(n + 1, |s|);
        assert vm1.GetStack() == vm2.GetStack();
        assert vm2.Gas() == vm1.Gas() -  Gas.G_VERYLOW;
        assert vm2.Gas() < vm1.Gas();
    }
}
