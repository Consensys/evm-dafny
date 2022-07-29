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
module Gas {
    const G_zero : int := 0;
	const G_base : int := 2;
	const G_verylow : int := 3;
	const G_low : int := 5;
	const G_mid : int := 8;
	const G_high : int := 10;
	const G_extcode : int := 700;
	const G_balance : int := 400;
	const G_sload : int := 200;
	const G_jumpdest : int := 1;
	const G_sset : int := 20000;
	const G_sreset : int := 5000;
	const R_sclear : int := 15000;
	const R_selfdestruct : int := 24000;
	const G_selfdestruct : int := 5000;
	const G_create : int := 32000;
	const G_codedeposit : int := 200;
	const G_call : int := 700;
	const G_callvalue : int := 9000;
	const G_callstipend : int := 2300;
	const G_newaccount : int := 25000;
	const G_exp : int := 10;
	const G_expbyte : int := 50;
	const G_memory : int := 3;
	const G_txcreate : int := 32000;
	const G_txdatazero : int := 4;
	const G_txdatanonzero : int := 68;
	const G_transaction : int := 21000;
	const G_log : int := 375;
	const G_logdata : int := 8;
	const G_logtopic : int := 375;
	const G_sha3 : int := 30;
	const G_sha3word : int := 6;
	const G_copy : int := 3;
	const G_blockhash : int := 20;
	const G_quaddivisor : int := 100;

}
