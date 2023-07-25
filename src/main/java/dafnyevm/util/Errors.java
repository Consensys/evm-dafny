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
package dafnyevm.util;

import evmtools.core.Transaction;

public class Errors {
    public static Transaction.Outcome toErrorCode(EvmState.Error err) {
        if (err instanceof EvmState.Error_REVERTS) {
            return Transaction.Outcome.REVERT;
        } else if (err instanceof EvmState.Error_INSUFFICIENT__GAS) {
            return Transaction.Outcome.OUT_OF_GAS;
        } else if (err instanceof EvmState.Error_INVALID__OPCODE) {
            return Transaction.Outcome.INVALID_OPCODE;
        } else if (err instanceof EvmState.Error_INVALID__JUMPDEST) {
            return Transaction.Outcome.INVALID_JUMPDEST;
        } else if (err instanceof EvmState.Error_STACK__OVERFLOW) {
            return Transaction.Outcome.STACK_OVERFLOW;
        } else if (err instanceof EvmState.Error_STACK__UNDERFLOW) {
            return Transaction.Outcome.STACK_UNDERFLOW;
        } else if (err instanceof EvmState.Error_MEMORY__OVERFLOW) {
            return Transaction.Outcome.MEMORY_OVERFLOW;
        } else if (err instanceof EvmState.Error_RETURNDATA__OVERFLOW) {
            return Transaction.Outcome.RETURNDATA_OVERFLOW;
        } else if (err instanceof EvmState.Error_INSUFFICIENT__FUNDS) {
            return Transaction.Outcome.INSUFFICIENT_FUNDS;
        } else if (err instanceof EvmState.Error_CALLDEPTH__EXCEEDED) {
            return Transaction.Outcome.CALLDEPTH_EXCEEDED;
        } else if (err instanceof EvmState.Error_CODESIZE__EXCEEDED) {
            return Transaction.Outcome.CODESIZE_EXCEEDED;
        } else if (err instanceof EvmState.Error_ACCOUNT__COLLISION) {
            return Transaction.Outcome.ACCOUNT_COLLISION;
        } else if (err instanceof EvmState.Error_WRITE__PROTECTION__VIOLATED) {
            return Transaction.Outcome.WRITE_PROTECTION;
        } else {
            return Transaction.Outcome.UNKNOWN;
        }
    }
}
