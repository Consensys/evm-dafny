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

module Optional {

    datatype Option<T> = Some(v: T) | None {
        /**
         * Extract the value contained within this option.
         */
        function Unwrap() : T
        requires this.Some? {
            this.v
        }

        /**
         * Returns the contained value (if it exists) or the default value
         * (otherwise).
         */
        function UnwrapOr(default: T) : T {
            match this
            case Some(v) => v
            case none => default
        }
    }
}
