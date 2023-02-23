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

module Arrays {
    import opened Int
    /**
     * A fixed size array which is bounded by the maximum word size.  Thus, it
     * represents an array (e.g. of bytes) which could appear as part of the EVM
     * state (e.g. CALLDATA or RETURDATA).  Thus, the length of the array can be
     * reasonably turned into a u256 and (for example) loaded on the stack.
     */
    type Array<T> = arr:seq<T> | |arr| < TWO_256
}
