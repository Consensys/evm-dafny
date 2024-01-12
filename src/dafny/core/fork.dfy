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
include "../../../libs/DafnyCrypto/src/dafny/util/option.dfy"
include "../opcodes.dfy"
include "../util/int.dfy"

module EvmFork {
    import opened Int
    import opened Opcode
    import opened Optional

    const GENISIS_BYTECODES : set<u8> := {
	    // 0s: Stop and Arithmetic Operations
        STOP,ADD,MUL,SUB,DIV,SDIV,MOD,SMOD,ADDMOD,MULMOD,EXP,SIGNEXTEND,
	    // 10s: Comparison & Bitwise Logic Operations
	    LT,GT,SLT,SGT,EQ,ISZERO,AND,OR,XOR,NOT,BYTE,SHL,SHR,SAR,
	    // 20s: SHA3
	    KECCAK256,
	    // 30s: Environment Information
	    ADDRESS,BALANCE,ORIGIN,CALLER,CALLVALUE,CALLDATALOAD,CALLDATASIZE,CALLDATACOPY,
        CODESIZE,CODECOPY,GASPRICE,EXTCODESIZE,EXTCODECOPY,RETURNDATASIZE,RETURNDATACOPY,
        EXTCODEHASH,
	    // 40s: Block Information
	    BLOCKHASH,COINBASE,TIMESTAMP,NUMBER,DIFFICULTY,GASLIMIT,CHAINID,SELFBALANCE,
	    // 50s: Stack, Memory Storage and Flow Operations
	    POP,MLOAD,MSTORE,MSTORE8,SLOAD,SSTORE,JUMP,JUMPI,PC,MSIZE,GAS,JUMPDEST,
	    // 60s & 70s: Push Operations
	    PUSH1,PUSH2,PUSH3,PUSH4,PUSH5,PUSH6,PUSH7,PUSH8,PUSH9,PUSH10,PUSH11,
        PUSH12,PUSH13,PUSH14,PUSH15,PUSH16,PUSH17,PUSH18,PUSH19,PUSH20,PUSH21,
	    PUSH22,PUSH23,PUSH24,PUSH25,PUSH26,PUSH27,PUSH28,PUSH29,PUSH30,PUSH31,
	    PUSH32,
	    // 80s: Duplication Operations
	    DUP1,DUP2,DUP3,DUP4,DUP5,DUP6,DUP7,DUP8,DUP9,DUP10,DUP11,DUP12,DUP13,
	    DUP14,DUP15,DUP16,
	    // 90s: Exchange Operations
	    SWAP1,SWAP2,SWAP3,SWAP4,SWAP5,SWAP6,SWAP7,SWAP8,SWAP9,SWAP10,SWAP11,
	    SWAP12,SWAP13,SWAP14,SWAP15,SWAP16,
	    // a0s: Logging Operations
	    LOG0,LOG1,LOG2,LOG3,LOG4,
        // e0s
        EOF,
	    // f0s: System operations
	    CREATE,CALL,CALLCODE,RETURN,
	    DELEGATECALL,CREATE2,STATICCALL,
	    REVERT,INVALID,SELFDESTRUCT
    }

    // ===================================================================
    // EIPS
    // ===================================================================

    // An EIP consists of an identifying number, and a description.
    type EIP = (nat,string)

    function EipDescription(eip: nat) : Option<string> {
        match eip
        case 1559 => Some("Fee market change for ETH 1.0 chain")
        case 2565 => Some("ModExp Gas Cost")
        case 2929 => Some("Gas cost increases for state access opcodes")
        case 2718 => Some("Typed Transaction Envelope")
        case 2930 => Some("Optional access lists")
        case 3198 => Some("BASEFEE opcode")
        case 3529 => Some("Reduction in refunds")
        case 3541 => Some("Reject new contract code starting with the 0xEF byte")
        case 3554 => Some("Difficulty Bomb Delay to December 2021")
        case 3651 => Some("Warm COINBASE")
        case 3675 => Some("Upgrade consensus to Proof-of-Stake")
        case 3855 => Some("PUSH0 instruction")
        case 3860 => Some("Limit and meter initcode")
        case 4345 => Some("Difficulty Bomb Delay to June 2022")
        case 4399 => Some("Supplant DIFFICULTY opcode with PREVRANDAO")
        case 4895 => Some("Beacon chain push withdrawals as operations")
        case 5133 => Some("Delaying Difficulty Bomb to mid-September 2022")
        case _ => None
    }

    // Updates the set of active bytecodes based on the effect of a sequence of
    // given eips.  Observe that EIPs are applied in order of occurrence.
    function EipBytecodes(eips: seq<nat>, bytecodes: set<u8>) : set<u8> {
        if |eips| == 0 then bytecodes
        else
            match eips[0]
            case 3198 => EipBytecodes(eips[1..], bytecodes + {BASEFEE})
            case 3855 => EipBytecodes(eips[1..], bytecodes + {PUSH0})
            case _ => EipBytecodes(eips[1..], bytecodes)
    }

    // ===================================================================
    // Forks
    // ===================================================================

    const BERLIN_EIPS : seq<nat> := [2565,2929,2718,2930]
    const LONDON_EIPS : seq<nat> := BERLIN_EIPS + [1559,3198,3529,3541,3554]
    const SHANGHAI_EIPS : seq<nat> := LONDON_EIPS + [3651,3855,3860,4895]      

    const BERLIN_BYTECODES : set<u8> := EipBytecodes(BERLIN_EIPS,GENISIS_BYTECODES)
    const LONDON_BYTECODES : set<u8> := EipBytecodes(LONDON_EIPS,GENISIS_BYTECODES)
    const SHANGHAI_BYTECODES : set<u8> := EipBytecodes(SHANGHAI_EIPS,GENISIS_BYTECODES)      

    const BERLIN : Fork := Instance(2021_04_15, BERLIN_EIPS, BERLIN_BYTECODES)
    const LONDON : Fork := Instance(2021_08_05, LONDON_EIPS, LONDON_BYTECODES)
    // Paris?
    const SHANGHAI : Fork := Instance(2023_04_12, SHANGHAI_EIPS, SHANGHAI_BYTECODES)      

    // A fork is either the _root_ (i.e. genisis EVM), or an _instance_ which
    // refines another fork.
    datatype Fork = Instance(id: nat, eips: seq<nat>, bytecodes: set<u8>) {
        // Determine whether or not a given EIP is active in this fork.
        predicate IsActive(eip: nat) { eip in this.eips }

        // Determine whether or not a given bytecode is active in this fork.
        // For example, BASEFEE is not active in (or before) Berlin but is
        // active in (and after) London.
        predicate IsBytecode(opcode: u8) { opcode in bytecodes }
    }

    // ===================================================================
    // Lemmas
    // ===================================================================
    lemma {:verify false} BerlinFacts()
    ensures BASEFEE !in BERLIN_BYTECODES
    {

    }

    lemma {:verify false} LondonFacts()
    ensures BASEFEE in LONDON_BYTECODES
    {

    }

    lemma {:verify false} ShanghaiFacts()
      ensures {PUSH0,BASEFEE} <= SHANGHAI_BYTECODES
    {

    }    
}
