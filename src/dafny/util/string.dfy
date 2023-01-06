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

include "./int.dfy"

module StringHelper {

    import opened Int

    /** Hexadecimal string. */
    type IntString = s: string | 
                        && |s| > 0 
                        && (|s| > 1 ==> s[0] != '0') 
                        && forall i | 0 <= i < |s| :: s[i] in "0123456789"
                        witness "1"

    const mapIntString := ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]

    /**
     *  Convert a nat into a string.
     */
    function method natToString(n: nat): IntString 
    {
        if n <= 9 then 
            mapIntString[n] 
        else 
            natToString(n / 10) + mapIntString[n % 10]
        // match n
        //     case 0 => "0" 
        //     case 1 => "1" 
        //     case 2 => "2" 
        //     case 3 => "3" 
        //     case 4 => "4"
        //     case 5 => "5" 
        //     case 6 => "6" 
        //     case 7 => "7" 
        //     case 8 => "8" 
        //     case 9 => "9"
        //     case _ => natToString(n / 10) + natToString(n % 10)
    }



    /**
     *  Whether a character is within 0-f.
     *  @todo   What about A-F?
     *  @param t variables 
     */
    function method IsHexDigit(c: char) : bool {
        '0' <= c <= '9' || 'a' <= c <= 'f'
    }

    /**
     *  Convert an integer [0,15] to a Hex.
     */
    function method ToHex(k: u8): (c: char) 
        requires 0 <= k <= 15
        ensures IsHexDigit(c)
    {
        if k <= 9 then '0' + k as char 
        else 'a' + (k - 10) as char
    }

    /**
     *  Convert a u8 to 2-char string.
     */
    function method U8ToHex(k: u8): (s: string)
        ensures |s| == 2
        ensures IsHexDigit(s[0])
        ensures IsHexDigit(s[1])
    {
        [ToHex(k / 16), ToHex(k % 16)] 
    }

    /**
     *  Convert a nat to a Hex String.
     */
    function method {:tailrecursion true} NatToHex(k: nat): (s: string)
        ensures |s| % 2 == 0
        ensures forall i :: 0 <= i < |s| ==> IsHexDigit(s[i])
        decreases k
    {
        if k <= 255 then U8ToHex((k % 256) as u8)
        else 
            NatToHex(k / 256) + U8ToHex((k % 256) as u8)
    }

    /**
     *  Whether a string is made of Hex digits.
     */
    predicate method IsHexString(s: string) 
    {
        forall i:: 0 <= i < |s| ==> IsHexDigit(s[i])
    }

    /**
     *  Convert a 2-char string to u8.
     */
    function method StringToHex(s: string): (k: u8) 
        requires |s| == 2
        requires IsHexDigit(s[0])
        requires IsHexDigit(s[1])
    {
        ToHexDigit(s[0]) * 16 + ToHexDigit(s[1])
    }

    
    /**
     *  Convert a Hex Digit to a u8.
     */
    function method ToHexDigit(c: char) : u8
    requires IsHexDigit(c) {
        if '0' <= c <= '9' then (c - '0') as u8
        else ((c - 'a') as u8) + 10
    }


}