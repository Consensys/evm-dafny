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
include "../../../dafny/evmstate.dfy"

/**
 *  Provide some tests to check some qualitative properties of bytecode.
 */
module Kontract1 {

    import opened Int
    import opened Bytecode
    import opened EvmBerlin
    import opened EvmState
    import opened Opcode
    import Stack
    import Gas

    /** Simple code that increments storage at location 0. */
    const INC_CONTRACT := Code.Create(
        [
        // Put STORAGE[0] and add one
        // 0x00   0x01  0x02   0x03   0x04  0x05 <- PC
           PUSH1, 0x00, SLOAD, PUSH1, 0x01, ADD,
        // If result is 0 then there is an overflow and we revert
        // 0x06  0x07   0x08 0x09   0x0a   0x0b  0x0c   0x0d  0x0e <- PC
           DUP1, PUSH1, 0xf, JUMPI, PUSH1, 0x00, PUSH1, 0x00, REVERT,
        // Otherwise, STORAGE[0] = STORAGE[0] + 1
        // 0xf       0x10   0x11  0x12    0x13 <- PC
           JUMPDEST, PUSH1, 0x00, SSTORE, STOP
        ]
    );

    /**
     *  Simple proof about a contract reverting if oevrflows.
     */
    method inc_proof(st: ExecutingState) returns (st': State)
        /** Initial state with PC = 0 and empty stack. */
        requires st.PC() == 0 && st.Operands() == 0
        /** Enough gas. */
        requires st.Gas() >= 40000
        /** Permission to write to storage. */
        requires st.WritesPermitted()
        /** Code is INC_CONTRACT. */
        requires st.evm.code == INC_CONTRACT
        /** The contract never runs out of gas. */
        ensures st'.REVERTS? || st'.RETURNS?
        /** It terminates normally iff storage at loc 0 is < MAX_U256. */
        ensures st'.RETURNS? <==> (st.Load(0) as nat) < MAX_U256
        /** The world state's accounts do not change. */
        ensures st'.RETURNS? ==> st'.world.accounts.Keys == st.evm.world.accounts.Keys
        /** Normal termination implies storage at Loc 0 has been incremented by 1. */
        ensures st'.RETURNS? ==> st'.world.Read(st.evm.context.address,0) as nat == st.Load(0) as nat + 1
    {
        //  Execute 7 steps (PUSH1, 0x00, SLOAD, PUSH1, 0x01, ADD, DUP1, PUSH1, 0xf, JUMPI)
        st' := ExecuteN(st,7);
        // Peek(0) == 0 iff an overflow occurred in the increment.
        if st'.Peek(0) == 0 {
            assert st'.PC() == 0xa;
            st' := ExecuteN(st',3);
            assert st'.REVERTS?;
        } else {
            assert st'.PC() == 0xf;
            st' := ExecuteN(st',4);
            assert st'.RETURNS?;
        }
    }

    /** Necessary and sufficient  conditoin for detecting overflow
     *  in ADD.
     */
    lemma AddOverflowNSC(x: u256, y: u256)
        ensures x as nat + y as nat > MAX_U256
            <==> (x as nat + y as nat) % TWO_256 < x as nat
    {
        //  Thanks Dafny
    }

    /** Code snippet that detects overflow in addition. */
    const OVERFLOW_CHECK := Code.Create(
        [
        // 0x00  0x01            //  stack
            DUP2, ADD,           //  [y + x, y] .
        // 0x02   0x03
            LT,                  //  [x + y < y?1:0]
        // 0x03
            PUSH1, 0x07, JUMPI,  //  [0x07, x < x + y?1:0]
        // If Peek(1) is 0 no overflow, STOP, otherwise JUMP and revert.
        // 0x06
            STOP,
        // 0x07      0x08   0x09  0x10   0x11, 0x12
            JUMPDEST, PUSH1, 0x00, PUSH1, 0x00, REVERT
        ]
    );

    /**
     *  This is a pattern that is frequently used to detect overflows for ADD.
     *
     *  @param  st  A state.
     *  @param  x   A u256.
     *  @param  y   A u256.
     *  @returns    A normal state with `x + y` top of stack if no overflow, a
     *              revert state otherwise..
     *  @note       The check relies on the property specified by lemma AddOverflowNSC.
     *  @note       The overflow is specified as x + y exceeding MAX_U256.
     */
    method OverflowCheck(st: ExecutingState, x: u256, y: u256) returns (st': State)
        /** OK state and initial PC.  */
        requires /* Pre0 */ st.PC() == 0
        /** Enough gas. Longest path gas-wise is via JUMPI. */
        requires /* Pre1 */ st.Gas() >= 6 * Gas.G_VERYLOW + Gas.G_HIGH + Gas.G_JUMPDEST
        /** Initial stack is [x, y]. */
        requires /* Pre2 */ st.GetStack() == Stack.Make([x, y]);
        /** The code is the snippet to detect overflow. */
        requires st.evm.code == OVERFLOW_CHECK
        /** The contract never runs out of gas thanks to Pre1. */
        ensures st'.REVERTS? || st'.RETURNS?
        /** Should revert iff overflow. */
        ensures st'.REVERTS? <==> x as nat + y as nat > MAX_U256
        /** Normal termination iff no overflow. */
        ensures st'.RETURNS? <==> x as nat + y as nat <= MAX_U256
    {
        //  Execute 4 steps -- DUP2 ADD LT PUSH1 0x07
        st' := ExecuteN(st,4);
        //  Depending on result of LT comparison overflow or not
        if st'.Peek(1) == 0 {
            st':= Execute(st');
            assert st'.PC() == 0x06;
            st' := ExecuteN(st',1);
            assert st'.RETURNS?;
        } else {
            st':= Execute(st');
            assert st'.PC() == 0x07;
            st' := ExecuteN(st',4);
            assert st'.REVERTS?;
        }
    }

    /**
     *  A progrqm with a loop.
     *
     *  @param  c   The number of times to iterate the loop.
     *
     *  @note       The code iterates a loop `c` times by decremeting
     *              a copy of `c` until it is zero.
     *              We prove termination on this program and also
     *              that it ends in a RETURN state.
     *
     *              The stack content is unconstrained but there must be
     *              enough capacity (3) to perform this computation.
     */
    method Loopy(st: ExecutingState, c: u8) returns (st': State)
        requires /* Pre0 */ st.PC() == 0 && st.Capacity() >= 3
        requires /* Pre1 */ st.Gas() >=
            3 * Gas.G_VERYLOW + Gas.G_JUMPDEST +
            c as nat * (2 * Gas.G_HIGH + 2 * Gas.G_JUMPDEST + 6 * Gas.G_VERYLOW)
            + Gas.G_HIGH

        requires /* Pre2 */ st.evm.code == Code.Create(
            [
            //  0x00   0x01
                PUSH1, c,
            //  0x02,     0x03   0x04 0x05
                JUMPDEST, DUP1, PUSH1, 0x08,
            //  0x06
                JUMPI,
            //  0x07
                STOP,
            //  0x08      0x09   0x0a
                JUMPDEST, PUSH1, 0x01,
            //  0x0b   0x0c
                SWAP1, SUB,
            //  0x0d   0x0e  0x0f
                PUSH1, 0x02, JUMP
            ]
        );

        ensures /* Post0 */ st'.RETURNS?
    {
        //  Execute PUSH1, c, JUMPDEST, DUP1, PUSH1, 0x08
        st' := ExecuteN(st, 4);
        assert st'.EXECUTING?;
        //  verification variable to track decreasing counter.
        ghost var count : u256 := c as u256;
        //  number of times we get into the loop.
        ghost var n: nat := 0;

        while st'.Peek(2) > 0
            invariant st'.EXECUTING?
            invariant st'.Gas() >= count as nat * (2 * Gas.G_HIGH + 2 * Gas.G_JUMPDEST + 6 * Gas.G_VERYLOW) + Gas.G_HIGH
            invariant st'.PC() == 0x06
            invariant st'.Operands() > 2
            invariant count == st'.Peek(2) == st'.Peek(1)
            invariant st'.Peek(0) == 0x08;
            invariant st'.evm.code == st.evm.code
            invariant n == c as nat - count as nat
            decreases st'.Peek(2)
        {
            assert st'.PC() == 0x06;
            //  Execute body of the loop. 10 steps.
            st':= ExecuteN(st' ,10);
            count := count - 1;
            n := n + 1;
        }
        assert st'.PC() == 0x06;
        //  Check we iterated the loop c times.
        assert n == c as nat;
        //  JUMPI, STOP
        st' := ExecuteN(st', 2);
    }
}
