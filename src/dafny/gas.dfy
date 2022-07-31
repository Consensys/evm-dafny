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
 include "util/int.dfy"
 include "opcodes.dfy"

module Gas {

	import opened Int
	import opened Opcode

    const G_zero : nat := 0;
	const G_base : nat := 2;
	const G_verylow : nat := 3;
	const G_low : nat := 5;
	const G_mid : nat := 8;
	const G_high : nat := 10;
	const G_extcode : nat := 700;
	const G_balance : nat := 400;
	const G_sload : nat := 200;
	const G_jumpdest : nat := 1;
	const G_sset : nat := 20000;
	const G_sreset : nat := 5000;
	const R_sclear : nat := 15000;
	const R_selfdestruct : nat := 24000;
	const G_selfdestruct : nat := 5000;
	const G_create : nat := 32000;
	const G_codedeposit : nat := 200;
	const G_call : nat := 700;
	const G_callvalue : nat := 9000;
	const G_callstipend : nat := 2300;
	const G_newaccount : nat := 25000;
	const G_exp : nat := 10;
	const G_expbyte : nat := 50;
	const G_memory : nat := 3;
	const G_txcreate : nat := 32000;
	const G_txdatazero : nat := 4;
	const G_txdatanonzero : nat := 68;
	const G_transaction : nat := 21000;
	const G_log : nat := 375;
	const G_logdata : nat := 8;
	const G_logtopic : nat := 375;
	const G_sha3 : nat := 30;
	const G_sha3word : nat := 6;
	const G_copy : nat := 3;
	const G_blockhash : nat := 20;
	const G_quaddivisor : nat := 100;

}
