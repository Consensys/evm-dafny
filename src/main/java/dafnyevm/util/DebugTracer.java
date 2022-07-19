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

import EVM_Compile.T;
import dafnyevm.DafnyEvm;
import dafnyevm.DafnyEvm.State;

public class DebugTracer extends DafnyEvm.TraceAdaptor {

	@Override
	public void step(State state) {
		System.err.println(state);
	}

}
