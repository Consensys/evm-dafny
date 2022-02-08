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

include "NonNativeTypes.dfy"

/**
 *  Not used yet.
 */
module EVMInst {

    import opened NonNativeTypes

    type EVMStack = seq<uint256>

    method push1(s: EVMStack, v: uint256) returns (s': EVMStack)

    method pop(s: EVMStack, v: uint256) returns (s': EVMStack)

    method add(s: EVMStack) returns (s': EVMStack)


}