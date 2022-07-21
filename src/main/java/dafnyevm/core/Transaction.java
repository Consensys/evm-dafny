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
package dafnyevm.core;

import java.math.BigInteger;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import dafnyevm.util.Hex;

public class Transaction {
	public final BigInteger sender;
	public final BigInteger to;
	/**
	 * Maximum amount of gas to expend trying to complete the transaction.
	 */
	public final BigInteger gasLimit;
	/**
	 * Price per unit of Gas (in Wei).
	 */
	public final BigInteger gasPrice;

	public final BigInteger nonce;
	/**
	 * Funds being transferred (in Wei)
	 */
	public final BigInteger value;
	/**
	 * Call data provided for the contract call (e.g. which typically follows the
	 * Solidity ABI).
	 */
	public final byte[] data;

	public Transaction(BigInteger sender, BigInteger to, BigInteger gasLimit, BigInteger gasPrice, BigInteger nonce,
			BigInteger value, byte[] data) {
		this.sender = sender;
		this.to = to;
		this.gasLimit = gasLimit;
		this.gasPrice = gasPrice;
		this.nonce = nonce;
		this.value = value;
		this.data = data;
	}

	/**
	 * Parse transaction information from a JSON input file, as used by state tests
	 * found in the Ethereum Reference Tests.
	 *
	 * @param tx
	 * @return
	 */
	public static Transaction fromJSON(JSONObject json) throws JSONException {
		BigInteger to = Hex.toBigInt(json.getString("to"));
		BigInteger sender = Hex.toBigInt(json.getString("sender"));
		BigInteger gasPrice = Hex.toBigInt(json.getString("gasPrice"));
		// BigInteger gasLimit = Hex.toBigInt(json.getString("gasLimit"));
		BigInteger nonce = Hex.toBigInt(json.getString("nonce"));
		BigInteger value = parseValueArray(json.getJSONArray("value"));
		byte[] data = parseDataArray(json.getJSONArray("data"));
		// FIXME: need to figure out the meaning of the gas limit.
		return new Transaction(sender, to, null, gasPrice, nonce, value, data);
	}


	public static byte[] parseDataArray(JSONArray json) throws JSONException {
		byte[][] bytes = new byte[json.length()][];
		for(int i=0;i!=json.length();++i) {
			bytes[i] = Hex.toBytes(json.getString(i));
		}
		//
		return flattern(bytes);
	}

	public static BigInteger parseValueArray(JSONArray json) throws JSONException {
		if(json.length() != 1) {
			// NOTE: am unsure why a value array would have more than one element.
			throw new IllegalArgumentException("invalid value array");
		}
		return Hex.toBigInt(json.getString(0));
	}

	/**
	 * Flattern a two dimensional byte array into a one dimensional byte array.
	 *
	 * @param bytes
	 * @return
	 */
	private static byte[] flattern(byte[][] bytes) {
		int n = 0;
		for (int i = 0; i != bytes.length; ++i) {
			n += bytes[i].length;
		}
		byte[] result = new byte[n];
		int m = 0;
		for (int i = 0; i != bytes.length; ++i) {
			byte[] ith = bytes[i];
			System.arraycopy(ith, 0, result, m, ith.length);
			m = m + ith.length;
		}
		return result;
	}
}
