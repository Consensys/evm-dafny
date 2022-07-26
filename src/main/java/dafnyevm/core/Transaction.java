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
import java.util.Map;

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
	 * A transaction template is a transaction parameterised on three values:
	 * <code>data</code>, <code>gasLimit</code> and <code>value</code>. For each of
	 * these items, a template has a predefined array of values. A transaction can
	 * then be instantiated from a template by providing a <i>index</i> into the
	 * array of each item.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Template {
		private final Transaction template;
		private final BigInteger[] gasLimits;
		private final BigInteger[] values;
		private final byte[][] datas;

		public Template(BigInteger sender, BigInteger to, BigInteger[] gasLimits, BigInteger gasPrice, BigInteger nonce,
				BigInteger[] values, byte[][] datas) {
			// Create the "templated" transaction which has empty slots for the
			// parameterised values.
			this.template = new Transaction(sender,to,null,gasPrice,nonce,null,null);
			this.gasLimits = gasLimits;
			this.values = values;
			this.datas = datas;
		}

		/**
		 * Instantiate a transaction with a given set of _indexes_. That is, indices
		 * which refer to the array of available values for each item.
		 *
		 * @param data
		 * @param gas
		 * @param value
		 * @return
		 */
		public Transaction instantiate(Map<String,Integer> indices) {
			int g = indices.get("gas");
			int d = indices.get("data");
			int v = indices.get("value");
			return new Transaction(template.sender, template.to, gasLimits[g], template.gasPrice, template.nonce,
					values[v], datas[d]);
		}

		/**
		 * Parse transaction template information from a JSON input file, as used by
		 * state tests found in the Ethereum Reference Tests.
		 *
		 * @param tx
		 * @return
		 */
		public static Template fromJSON(JSONObject json) throws JSONException {
			BigInteger to = Hex.toBigInt(json.getString("to"));
			BigInteger sender = Hex.toBigInt(json.getString("sender"));
			BigInteger gasPrice;
			if (json.has("gasPrice")) {
				gasPrice = Hex.toBigInt(json.getString("gasPrice"));
			} else {
				System.out.println("*** MISSING GAS PRICE");
				gasPrice = BigInteger.ZERO;
			}
			BigInteger nonce = Hex.toBigInt(json.getString("nonce"));
			BigInteger[] gasLimits = parseValueArray(json.getJSONArray("gasLimit"));
			BigInteger[] values = parseValueArray(json.getJSONArray("value"));
			byte[][] datas = parseDataArray(json.getJSONArray("data"));
			return new Template(sender, to, gasLimits, gasPrice, nonce, values, datas);
		}

	}


	public static byte[][] parseDataArray(JSONArray json) throws JSONException {
		byte[][] bytes = new byte[json.length()][];
		for(int i=0;i!=json.length();++i) {
			bytes[i] = Hex.toBytes(json.getString(i));
		}
		//
		return bytes;
	}

	public static BigInteger[] parseValueArray(JSONArray json) throws JSONException {
		BigInteger[] values = new BigInteger[json.length()];
		for(int i=0;i!=json.length();++i) {
			values[i] = Hex.toBigInt(json.getString(i));
		}
		return values;
	}
}
