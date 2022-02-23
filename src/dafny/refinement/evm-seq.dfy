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
 
/**
 *  Basic instructions of the EVM, with no jumps.
 */
module EVMSeq {

    /** Basic instruction in EVM. Termninating. */
    datatype EVMInst<!S> = 
        Inst(i : S -> S)
    
    /**
     *  Compute next state.
     *  
     *  @param  i   An instruction.
     *  @param  s   A state.
     *  @result     The state reached after executing `i` from `s`.
     */
    function method runInst<S>(i: EVMInst, s: S): S
    {
        match i 
            case Inst(e) => e(s)
    }

}
