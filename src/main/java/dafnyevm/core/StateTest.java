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

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.json.JSONException;
import org.json.JSONObject;

public class StateTest {
	public enum Expectation {
		/**
		 * Indicates test ran to completion, possibly producing output data.
		 */
		OK,
		/**
		 * Indicates not enough gas to start with!
		 */
		IntrinsicGas,
		/**
		 * Indicates out-of-gas.
		 */
		OutOfGas,
		/**
		 * Transaction type not supported (?).
		 */
		TypeNotSupported,
		/**
		 * Indicates test ran but caused a revert.
		 */
		REVERT,
		/**
		 * Indicates an outcome was not generated due to some kind of internal issue
		 * (e.g. fork not supported, transaction type not supported, etc).
		 */
		FAILURE
	}

	public final Map<String, Integer> indexes;
	public final Expectation expect;

	public StateTest(Map<String, Integer> indices, Expectation expect) {
		this.indexes = Collections.unmodifiableMap(indices);
		this.expect = expect;
	}

	public static StateTest fromJSON(JSONObject json) throws JSONException {
		JSONObject is = json.getJSONObject("indexes");
		HashMap<String, Integer> map = new HashMap<>();
		map.put("data", is.getInt("data"));
		map.put("gas", is.getInt("gas"));
		map.put("value", is.getInt("value"));
		Expectation kind;
		if (json.has("expectException")) {
			String except = json.getString("expectException");
			switch(except) {
			case "TR_IntrinsicGas": {
				kind = Expectation.IntrinsicGas;
				break;
			}
			case "TR_GasLimitReached": {
				kind = Expectation.OutOfGas;
				break;
			}
			case "TR_TypeNotSupported": {
				kind = Expectation.TypeNotSupported;
				break;
			}
			default:
				throw new RuntimeException("unrecognised exception: " + except);
			}
		} else {
			kind = Expectation.OK;
		}
		return new StateTest(map, kind);
	}

	public static class Outcome {
		public final String name;
		public final String fork;
		public final boolean pass;

		public Outcome(String name, String fork, boolean pass) {
			this.name = name;
			this.fork = fork;
			this.pass = pass;
		}

		/**
		 * Identifies whether this test was actually runnable. If not, then there would
		 * be no corresponding trace data generated for it. Otherwise, we can expecte
		 * trace data.
		 *
		 * @return
		 */
		public boolean wasRunnable() {
			return pass;
		}

		public static Outcome fromJSON(JSONObject json) throws JSONException {
			String name = json.getString("name");
			boolean pass = json.getBoolean("pass");
			String fork = json.getString("fork");
			return new Outcome(name, fork, pass);
		}
	}
}
