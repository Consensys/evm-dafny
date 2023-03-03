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
package dafnyevm.util;

import java.math.BigInteger;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONStringer;
import org.json.JSONWriter;

import evmtools.util.Bytecodes;
import evmtools.util.Hex;
import dafnyevm.DafnyEvm;

public class Tracers {

	/**
	 * Generate the default debug output.
	 *
	 */
	public static class Debug extends DafnyEvm.TraceAdaptor {

		@Override
		public void step(DafnyEvm.State.Executing state) {
			final String p = state.getPC().toString();
			final String o = Bytecodes.toString(state.getOpcode());
			final String m = Hex.toAbbreviatedHexString(state.getMemory());
			final String s = state.getStorage().toString();
			final String a = toStackString(state.getStack());
			String st = String.format("pc=%s (%s), stack=%s, memory=%s, storage=%s", p, o, a, m, s);
			System.out.println(st);
		}

		@Override
		public void exception(DafnyEvm.State.Exception state) {
			System.out.println("error");
		}

		@Override
		public void end(DafnyEvm.State.Return state) {
			System.out.println(Hex.toHexString(state.getReturnData()));
		}

		private String toStackString(BigInteger[] stack) {
			StringBuilder s = new StringBuilder();
			for(int i=0;i<stack.length;++i) {
				if(i != 0) {
					s.append(":");
				}
				s.append(Hex.toHexString(stack[i]));
			}
			return s.toString();
		}

        @Override
        public void enter() {

        }
	}

	/**
	 * Generate JSON output according to EIP-3155.
	 */
	public static class JSON extends DafnyEvm.TraceAdaptor {

		@Override
		public void step(DafnyEvm.State.Executing state) {
			JSONStringer json = new JSONStringer();
			try {
				JSONWriter obj = json.object();
				obj.key("pc").value(state.getPC());
				obj.key("op").value(state.getOpcode());
				obj.key("gas").value(Hex.toHexString(state.getGas()));
				if (state.getMemorySize() > 0) {
					byte[] mem = state.getMemory();
					obj.key("memory").value(Hex.toHexString(mem));
				}
				obj.key("memSize").value(state.getMemorySize());
				obj.key("stack").value(toStackArray(state.getStack()));
				// TODO: update this when internal contract calls are supported.
				obj.key("depth").value(1);
				System.out.println(obj.endObject().toString());
			} catch (JSONException e) {
				// In principle, this should never happen!
				throw new RuntimeException(e);
			}
		}

		@Override
		public void end(DafnyEvm.State.Return state) {
			JSONStringer json = new JSONStringer();
			try {
				JSONWriter obj = json.object();
				obj.key("output").value(Hex.toAbbreviatedHexString(state.getReturnData()));
				obj.key("gasUsed").value(Hex.toHexString(state.getGas()));
				System.out.println(obj.endObject().toString());
			} catch (JSONException e) {
				// In principle, this should never happen!
				throw new RuntimeException(e);
			}
		}

		@Override
		public void exception(DafnyEvm.State.Exception state) {
			JSONStringer json = new JSONStringer();
			try {
				JSONWriter obj = json.object();
				obj.key("gasUsed").value(Hex.toHexString(state.getGas()));
				System.out.println(obj.endObject().toString());
			} catch (JSONException e) {
				// In principle, this should never happen!
				throw new RuntimeException(e);
			}
		}

		/**
		 * Convert a Dafny sequece of UINT256 words into a JSON array for output.
		 *
		 * @param seq
		 * @return
		 */
		private JSONArray toStackArray(BigInteger[] stack) {
			JSONArray arr = new JSONArray();
			for(int i=0;i<stack.length;++i) {
				arr.put(Hex.toHexString(stack[i]));
			}
			return arr;
		}

        @Override
        public void enter() {

        }
	}

}
