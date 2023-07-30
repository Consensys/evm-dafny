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

include "evms/berlin.dfy"
include "core/precompiled.dfy"

 module t8n {
    import Storage
    import opened Int
    import Code
    import WorldState
    import Context
    import SubState
    import EvmState
    import EvmBerlin
    import Optional
    import Stack
    import Memory
        import Precompiled
    import opened Opcode

    method Main(argv: seq<string>){

        var gasAvailable : nat := 100;
        var argI := 1;
        while argI < |argv| {
            match argv[argI]
            case "help" =>
                print "T8n tool implemented in Dafny\n";
                return;
            case "--gas" =>
                if argI + 1 >= |argv| {
                    print "Missing arg for --gas\n";
                    return;
                }
                gasAvailable := str2nat(argv[argI+1]);
                argI := argI + 2;
                continue;
            case _ =>
                print "Unrecognized arg ", argv[argI], "\n";

            argI := argI + 1;
        }

        var emptyStorage := Storage.Create(map[]);
        var emptyCode := Code.Create([]);
        var someCode := Code.Create([PUSH1, 0x1, PUSH1, 0x2, ADD, PUSH1, 0x00, MSTORE, PUSH1, 0x20, PUSH1, 0x00, RETURN]);
        var emptyStack := Stack.EmptyEvmStack;
        var mem := Memory.Create();
        var substate := SubState.Create();


        //context
        var sender := 254;
        var origin := 243;
        var recipient := 221;
        var callValue := 1;
        var callData : seq<u8> := [12];
        var writePermission := true;
        var gasPrice := 12;
        var blockInfo := Context.Info(1,2,3,4,5,6);
        var context := Context.Create(sender, origin, recipient, callValue, callData, writePermission, gasPrice, blockInfo);

        var senderAccount := WorldState.Account(1,2,Storage.Create(map[]),emptyCode, 0);
        var recipientAccount := WorldState.Account(5,6,Storage.Create(map[]),someCode, 0);
        var accounts := map[sender := senderAccount, recipient := recipientAccount];
        var worldState := WorldState.Create(accounts);

        var gasLimit := 2;

        // DafnyEvm.create(address)
        var address : u160 := 20;
        var nonce := 4;
        var endowment := 5;
        var addresses : map<u256,u256> := map[ 100 := 2 ];

        var depth := 0;

        var st := EvmState.Call(worldState, context, Precompiled.DEFAULT, substate, recipient, callValue, gasAvailable, depth);

        MessageCall(sender, origin, recipient, callValue, callData, writePermission, gasPrice, blockInfo, accounts, gasAvailable);

    }

    method CreateAccount(worldStateOrig: map<u160, WorldState.Account>, address: u160, nonce:nat, endowment:u256, storage : map<u256,u256>) returns (ws: map<u160, WorldState.Account>) {
        //Storage_Compile.T store = Storage_Compile.T.create(new DafnyMap<BigInteger,//BigInteger>(storage));
        var store := Storage.Create(storage);
		//Code_Compile.Raw code = new Code_Compile.Raw(DafnySequence.fromBytes//(bytecode));
        var code := Code.Create([12]);
		//WorldState_Compile.Account acct = WorldState_Compile.__default.CreateAccount(nonce, endowment, store,code);
        var acct := WorldState.CreateAccount(nonce, endowment, store, code, WorldState.HASH_EMPTYCODE);
		//this.worldState = DafnyMap.update(worldState, address, acct);

        ws := worldStateOrig[address :=  acct];
    }

    method MessageCall(sender: u160, origin: u160, recipient: u160, callValue: u256, callData: seq<u8>, writePermission:bool, gasPrice: u256, blockInfo: Context.Block, accounts: map<u160, WorldState.Account>, gas:nat)
    requires sender in accounts
    requires |callData| <= MAX_U256
    requires accounts[sender].nonce  < MAX_U64
    {
        var ctx := Context.Create(sender, origin, recipient, callValue, callData, writePermission, gasPrice, blockInfo);
        var ws := WorldState.Create(accounts);
        var ss := SubState.Create();
        ss := ss.AccountAccessed(sender);
        ss := ss.AccountAccessed(recipient);
        ws := ws.IncNonce(sender);
        var st := EvmState.Call(ws, ctx, Precompiled.DEFAULT, ss, recipient, callValue, gas, 1);
        st := Run(0, st);
        if st.RETURNS? {

        }
        TracerStep(-1, st);
        //return st;
    }






    method TracerStep(depth: int, st: EvmState.State ) {
        //TODO
        match st
        case EXECUTING(_)  => print "PC:", st.evm.pc, " OP:", st.Decode(), " GAS:", st.Gas(), "\n";
        case _ => print "not running\n";
    }

    method /*{:extern}*/ CreateContractAddress(sender: u160, nonce: int, salt: Optional.Option<u256>, initCode: seq<u8>) returns (addr: u160)  {
        addr := 1234;
        //TODO extern
    }

    method {:extern} str2nat(str: string) returns (i: nat){
        i := 100;
    }


    method {:verify false} Run(depth: nat, st0: EvmState.State) returns (st: EvmState.State) {
        st := st0;
        while (st.EXECUTING?){
            TracerStep(depth, st);
            st := EvmBerlin.Execute(st);
            match st
                case CONTINUING(cc) => {
                    if cc.CALLS? {
                        st := CallContinue(depth, cc);
                    } else if cc.CREATES? {
                        st := CreateContinue(depth, cc);
                    }
                }
                case _ => { }
        }
        TracerStep(depth, st);
    }

    method {:verify false} CallContinue(depth: nat, cc: EvmState.Continuation) returns (st: EvmState.State)
        requires cc.CALLS?
        requires |cc.callData| <= MAX_U256
        // World state must contain this account
        requires cc.evm.world.Exists(cc.sender)
    {
        st := cc.CallEnter(depth);
        if !st.ERROR? || st.IsRevert() {
            st := Run(depth+1, st);
        }
        return cc.CallReturn(st);
    }

    method {:verify false} CreateContinue(depth: nat, cc: EvmState.Continuation) returns (st: EvmState.State)
        requires cc.CREATES? {
        var sender := cc.evm.context.address;
        var acct := cc.evm.world.accounts[sender];
        var nonce := acct.nonce - 1;
        //var hash := addr(sender, nonce, st.salt, st.initcode);
        var address : u160 := CreateContractAddress(sender, nonce, cc.salt, cc.initcode);
        st := cc.CreateEnter(depth, address, cc.initcode);
        st := Run(depth, st);
        return cc.CreateReturn(st, address);

    }
 }
