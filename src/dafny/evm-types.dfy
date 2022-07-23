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

include "util/memory.dfy"
include "util/storage.dfy"
include "util/stack.dfy"
include "util/context.dfy"
include "util/code.dfy"

/**
 * Provide a state type for the Ethereum Virtual Machine..
 */
module EVM_TYPES {

  	import opened Int
  	import Stack
  	import Memory
  	import Storage
  	import Context
  	import Code

	/**	Normal state of the Ethereum Virtual Machine. */
  	datatype T = EVM(
    	context: Context.T,
    	storage : Storage.T,
    	stack   : Stack.T,
    	memory  : Memory.T,
    	code: Code.T,
    	gas: nat,
    	pc : u256
  	)

	/**
	* Captures the possible state of the machine.  Normal execution is indicated
	* by OK (with the current machine data).  An exceptional halt is indicated by INVALID
	* (e.g. insufficient gas, insufficient stack operands, etc).  Finally, a RETURN or REVERT
	* with return data are indicated accordingly (along with any gas returned).
	*/
	datatype State = 
			OK(evm:T) 
		| 	INVALID 
		| 	RETURNS(gas:nat,data:seq<u8>) 
		| 	REVERT(gas:nat,data:seq<u8>) {
			//	Some useful functions
			predicate method IsFailure() { 
				!this.OK?
			} 
			function method PropagateFailure(): State
				requires IsFailure() {
				//	Propagate the failure
				this
			} 
			function method Extract(): T
				requires !IsFailure() {
				this.evm 
			}
		}
}
