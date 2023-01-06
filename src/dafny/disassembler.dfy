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

include "../dafny/opcodes.dfy"
include "../dafny/util/string.dfy"
include "../dafny/util/int.dfy"

module Dissassembler {

    import opened Int
    import opened StringHelper
    import Opcode 

    /**
     *  Items that can be in bytecode.
     */
    datatype Item = 
            Instr(address: nat, code: u8, args: string := "")
        |   Data(address: nat, value: u8)
        |   Error(address: nat, code: u8)
        

    datatype EVMProg = EVMProg(p: seq<Item>)
        {
            /**
            *  Pretty print to seq<u8., ready to use as `code` in the EVM.
            */
            function method PrintAsSeq(): seq<string> {
                seq(|p|, i requires 0 <= i < |p| => 
                    match p[i] 
                        case Instr(a, c, _) => Opcode.Decode(c)
                        case Data(a, v) => U8ToHex(v)
                        case Error(a, c) => U8ToHex(c)
                )
            }

            /**
            *  Skip Data and Error (and use the args in the instructions to pretty print).
            */
            function method {:tailrecursion true} PrettyPrint(index: nat := 0): seq<string> 
                decreases |p| - index
            {
                if index >= |p| then []
                else 
                    (match p[index]
                        case Instr(a, c, v) => ["0x" + NatToHex(a) + ": " + Opcode.Decode(c) + v] 
                        case _ => []
                    ) + PrettyPrint(index + 1)
            }
        }

    /**
     *  Number of Arguments expected by an opcode.  
     */
    function method ArgSize(k: u8): (n: nat)
        ensures 0 <= n <= 32
    {
        if 0x60 <= k <= 0x7f then 
            (k - 0x60) as nat + 1
        else 0
    }

    function method {:tailrecursion true} Assemble(xs: seq<u8>): (r: string)
        ensures |r| % 2 == 0 
    {
        if |xs| == 0 then ""
        else U8ToHex(xs[0]) + Assemble(xs[1..])
    }

    /**
     *  Dissassemble a string.
     */
    function method {:tailrecursion true} Dis(code: string): seq<string> 
        requires |code| % 2 == 0 
        requires forall i:: 0 <= i < |code| ==> IsHexDigit(code[i])
    {
        if |code| == 0 then []
        else 
            var nextInstr := Opcode.Decode(StringToHex(code[..2]));
            var numArgs := ArgSize(StringToHex(code[..2]));
            if |code[2..]| >= 2 * numArgs then 
                [nextInstr 
                    + 
                    (if numArgs >= 1 then 
                        " 0x" + code[2..2 + 2 * numArgs]
                    else ""
                    )
                    + "\n"
                ]
                    + Dis(code[2 + 2 * numArgs..])
            else 
                [Opcode.Decode(StringToHex(code[..2])) + "\n"] + ["Error"]
    }

    /**
     *  Build a seq of Item from a string.
     */
    function method {:tailrecursion true} Dis2(code: string, pc: nat := 0): seq<Item> 
        requires |code| % 2 == 0 
        requires forall i:: 0 <= i < |code| ==> IsHexDigit(code[i])
        decreases |code|
    {
        if |code| == 0  then []
        else 
            var nextInstr := StringToHex(code[..2]);
            var numArgs := ArgSize(StringToHex(code[..2]));
            if |code[2..]| >= 2 * numArgs then 
                [Instr(pc, nextInstr, if numArgs > 0 then " 0x" + code[2..2 + 2 * numArgs] else "")]
                + seq(numArgs, i requires 0 <= i < numArgs => 
                    Data(pc + i + 1, StringToHex(code[2..][2 * i..2 * (i + 1)])))
                + Dis2(code[2 + 2 * numArgs..], pc + 1 + numArgs)
            else 
                [Error(pc, nextInstr)] + Dis2(code[2..], pc + 1)
    }


}