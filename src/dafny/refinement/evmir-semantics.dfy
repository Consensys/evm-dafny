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

include "../utils/NativeTypes.dfy"
include "../utils/NonNativeTypes.dfy"
include "./evmir-types.dfy"

module EVMIRSemantics {

    import opened NativeTypes
    import opened NonNativeTypes
    import opened EVMIRTypes

    /**
     *  Compute next state.
     *  @param  i   An instruction.
     *  @param  s   A state.
     *  @result     The state reached after executing `i` from `s`.
     */
    function method runInst<S>(i: EVMInst<S>, s: S): S
    {
        match i 
            case Inst(e) => 
                e(s)
    }

    /**
     *  Semantics of EVM programs.
     */
    function method runEVM<S>(pc: nat, p: map<nat, EVM>, s: S, n: nat): (S, nat)
        decreases n 
    {
        if pc == 0 || n == 0 || pc !in p then (s, 0)
            //  We could have different types of termination
        else 
            //  Execute instruction at PC 
            match p[pc] 
                case AInst(Inst(i)) => 
                    runEVM(pc + 1, p, i(s), n - 1)
                case Jumpi(c, tgt) => 
                    if !c(s) then runEVM(pc + 1, p, s, n - 1) else runEVM(tgt, p, s, n - 1)
                case Jump(tgt) => 
                    runEVM(tgt, p, s, n - 1) 
    }


    /**
     *  Run n steps of the program.
     *  @param  p   A program.
     *  @param  s   A state.
     *  @param  n   The number of steps to execute.
     *  @returns    The state obtained after executing `n` steps of `p`. 
     */
    function method runEVMIR<S>(p: seq<EVMIR>, s: S, n: nat): S 
        decreases n - 1
    {   
        if n == 0 || p == [] then s 
            //  max number of steps reached or program has terminated. 
        else 
            match p[0] 
                case While(c, b) => 
                    if c(s) then runEVMIR(p, runInst(b, s) , n - 1)
                    else s
    }

    /**
    *  Negation of a boolean function.
    *  @param  f   A boolean function.
    *  @return     not(f) i.e. negF(x) = !f(x).
    */
    function negF<S>(f: S -> bool): S -> bool 
    { 
        x => !f(x) 
    }

}