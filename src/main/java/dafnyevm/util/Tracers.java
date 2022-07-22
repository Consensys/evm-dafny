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

import java.io.PrintStream;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONStringer;
import org.json.JSONWriter;

import EVM_Compile.State;
import EVM_Compile.State_OK;
import EVM_Compile.State_RETURNS;
import EVM_Compile.State_REVERTS;
import dafny.DafnySequence;
import dafnyevm.DafnyEvm;
import dafnyevm.DafnyEvm.Tracer;
import dafnyevm.core.Trace;
import dafnyevm.core.Trace.Step;

public class Tracers {

	/**
	 * The default tracer does nothing at all.
	 */
	public static final class Default implements Tracer {

		@Override
		public void step(State st) {
			if (st instanceof State_OK) {
				// Do nothing.
			} else if (st instanceof State_RETURNS) {
				State_RETURNS sr = (State_RETURNS) st;
				byte[] bytes = DafnySequence.toByteArray((DafnySequence<Byte>) sr.data);
				System.out.println(Hex.toHexString(bytes));
			} else if (st instanceof State_REVERTS) {
				State_REVERTS sr = (State_REVERTS) st;
				byte[] bytes = DafnySequence.toByteArray((DafnySequence<Byte>) sr.data);
				System.out.println(Hex.toHexString(bytes));
				System.out.println("error: execution reverted");
			} else {
				// TODO: add error information
				System.out.println("error");
			}
		}
	};

	/**
	 * Generate the default debug output.
	 *
	 */
	public static class Debug extends DafnyEvm.TraceAdaptor {

		@Override
		public void step(DafnyEvm.SnapShot state) {
			final String p = state.getPC().toString();
			final String m = Arrays.toString(state.getMemory());
			final String s = state.getStorage().toString();
			final String a = state.getStack().toString();
			String st = String.format("pc=%s, storage=%s, memory=%s, stack=%s", p, s, m, a);
			System.out.println(st);
		}

		@Override
		public void exception(BigInteger gasUsed) {
			System.out.println("error");
		}

		@Override
		public void end(byte[] output, BigInteger gasUsed) {
			System.out.println(Hex.toHexString(output));
		}

		@Override
		public void revert(byte[] output, BigInteger gasUsed) {
			System.out.println(Hex.toHexString(output));
			System.out.println("error: execution reverted");
		}
	}

	public static class Structured extends DafnyEvm.TraceAdaptor {
		private final List<Trace> out;

		public Structured(List<Trace> out) {
			this.out = out;
		}

		@Override
		public void step(DafnyEvm.SnapShot state) {
			int pc = state.getPC().intValueExact();
			byte[] memory = state.getMemory();
			BigInteger[] stack = (BigInteger[]) state.getStack().toRawArray();
			out.add(new Trace.Step(pc,stack,memory));
		}

		@Override
		public void end(byte[] output, BigInteger gasUsed) {
			out.add(new Trace.Returns(output));
		}

		@Override
		public void revert(byte[] output, BigInteger gasUsed) {
			out.add(new Trace.Reverts(output));
		}

		@Override
		public void exception(BigInteger gasUsed) {
			out.add(new Trace.Exception());
		}
	}

	/**
	 * Generate JSON output according to EIP-3155.
	 */
	public static class JSON extends DafnyEvm.TraceAdaptor {

		@Override
		public void step(DafnyEvm.SnapShot state) {
			JSONStringer json = new JSONStringer();
			try {
				JSONWriter obj = json.object();
				obj.key("pc").value(state.getPC());
				obj.key("op").value(state.getOpcode());
				obj.key("gas").value(Hex.toHexString(state.getRemainingGas()));
				byte[] mem = state.getMemory();
				if (mem.length > 0) {
					obj.key("memory").value(Hex.toHexString(mem));
				}
				obj.key("memSize").value(mem.length);
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
		public void end(byte[] output, BigInteger gasUsed) {
			JSONStringer json = new JSONStringer();
			try {
				JSONWriter obj = json.object();
				obj.key("output").value(Hex.toHexString(output));
				obj.key("gasUsed").value(Hex.toHexString(gasUsed));
				System.out.println(obj.endObject().toString());
			} catch (JSONException e) {
				// In principle, this should never happen!
				throw new RuntimeException(e);
			}
		}

		@Override
		public void revert(byte[] output, BigInteger gasUsed) {
			JSONStringer json = new JSONStringer();
			try {
				JSONWriter obj = json.object();
				obj.key("output").value(Hex.toHexString(output));
				obj.key("gasUsed").value(Hex.toHexString(gasUsed));
				obj.key("error").value("execution reverted");
				System.out.println(obj.endObject().toString());
			} catch (JSONException e) {
				// In principle, this should never happen!
				throw new RuntimeException(e);
			}
		}

		@Override
		public void exception(BigInteger gasUsed) {
			JSONStringer json = new JSONStringer();
			try {
				JSONWriter obj = json.object();
				obj.key("gasUsed").value(Hex.toHexString(gasUsed));
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
		private JSONArray toStackArray(DafnySequence<? extends BigInteger> seq) {
			JSONArray arr = new JSONArray();
			for(int i=seq.length()-1;i>=0;--i) {
				arr.put(Hex.toHexString(seq.select(i)));
			}
			return arr;
		}
	}

}
