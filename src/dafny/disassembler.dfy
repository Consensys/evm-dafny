include "opcodes.dfy"
include "../dafny/util/int.dfy"
include "../dafny/util/bytes.dfy"


import opened Opcode
import opened Int
import opened Bytes

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
function method u8ToHex(k: u8): (s: string)
    ensures |s| == 2
    ensures IsHexDigit(s[0])
    ensures IsHexDigit(s[1])
{
    [ToHex(k / 16), ToHex(k % 16)] 
}

/**
 *  Dissassemble.
 */
method {:verify false} Main(argv: seq<string>)
{
    if |argv| < 2 {
        print "error\n";
    } else if |argv[1]| % 2 == 0  {
        // var s := DA("0001603a63b1c2d4ff");
        var s := DA(argv[1]);
        for i: nat := 0 to |s| {
            print s[i];
        }
    } else {
        print "error not even number of characters\n";
    }
    

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
 *  Number of Arguments expected by an opcode.  
 */
function method ArgSize(k: u8): (n: nat)
    ensures 0 <= n <= 16
{
     match k 
        case 0x60 => 1
        case 0x63 => 4
        case _ => 0
}

/**
 *  Decode an opcode.
 */
function method Decode(k: u8): string
{
    match k 
        case 0x00 => "STOP"
        case 0x01 => "ADD"
        case 0x60 => "PUSH1"
        case 0x63 => "PUSH4"
        case _ => "NA"
}

/**
 *  Dissassemble a string.
 */
function method {:tailrecursion true} DA(code: string): seq<string> 
    requires |code| % 2 == 0 
    requires forall i:: 0 <= i < |code| ==> IsHexDigit(code[i])
{
    if |code| == 0 then []
    else 
        var nextInstr := Decode(StringToHex(code[..2]));
        var numArgs := ArgSize(StringToHex(code[..2]));
        if |code[2..]| >= 2 * numArgs then 
            [Decode(StringToHex(code[..2])) 
                + 
                (if numArgs >= 1 then 
                    " 0x" + code[2..2 + 2 * numArgs]
                 else ""
                )
                + "\n"
            ]
                + DA(code[2 + 2 * numArgs..])
        else 
            [Decode(StringToHex(code[..2])) + "\n"] + ["Error"]

}

//  Previous version

/**
 *  Convert a Hex Digit to a u8.
 */
function method ToHexDigit(c: char) : u8
requires IsHexDigit(c) {
    if '0' <= c <= '9' then (c - '0') as u8
    else ((c - 'a') as u8) + 10
}

/**
 *  Convert a list of chars to a list of u8.
 */
function method convert(chars: seq<char>) : seq<u8>
requires |chars| % 2 == 0
requires forall i :: 0 <= i < |chars| ==> IsHexDigit(chars[i]) {
    if |chars| == 0 then []
    else
        var b := (ToHexDigit(chars[0]) * 16) + ToHexDigit(chars[1]);
        [b] + convert(chars[2..])
}

method ConvertToSeqU8(chrs: seq<char>) returns (seqU8: seq<u8>)
requires |chrs| % 2 == 0
requires forall i :: 0 <= i < |chrs| ==> IsHexDigit(chrs[i]) {
    var i:= 0;
    var accum: seq<u8> := [];
    while i + 1 < |chrs|
        invariant i % 2 == 0
        invariant forall j:: 0 <= j < |accum| ==> 0 <= accum[j] <= 255
        invariant i < |chrs| ==> |accum| * 2 == |chrs[..i]|
        {
            var b := (ToHexDigit(chrs[i]) * 16) + ToHexDigit(chrs[i + 1]);
            accum := accum + [b];
            i := i + 2;   
        }
    return accum;
}

function method ToHexByte(high: char, low: char) : u8
requires IsHexDigit(high) && IsHexDigit(low) {
    (ToHexDigit(high) * 16) + ToHexDigit(low)
}

function method convertToSeqHex(chars: seq<char>) : seq<u8>
requires |chars| % 2 == 0
requires forall i :: 0 <= i < |chars| ==> IsHexDigit(chars[i]) {
    // Determine number of characters
    var n := |chars| / 2;
    // Construct sequences
    seq(n, i requires i >= 0 && i < n => ToHexByte(chars[i*2],chars[(i*2)+1]))
}

function method seqU8ToStringHex(seqU8: seq<u8>, accum: string): string
    {
        if seqU8 == []
            then accum
        else 
            u8ToHex(seqU8[0]) + seqU8ToStringHex(seqU8[1..], accum)  
    }

type stringNat = s: string | |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
                        forall i | 0 <= i < |s| :: s[i] in "0123456789"
                        witness "1"

function method natToString(n: nat): stringNat 
    {
        match n
            case 0 => "0" 
            case 1 => "1" 
            case 2 => "2" 
            case 3 => "3" 
            case 4 => "4"
            case 5 => "5" 
            case 6 => "6" 
            case 7 => "7" 
            case 8 => "8" 
            case 9 => "9"
            case _ => natToString(n / 10) + natToString(n % 10)
  }

function method stringToNat(s: stringNat): nat
    decreases |s|
    {
        if |s| == 1 
            then
                match s[0]
                    case '0' => 0 
                    case '1' => 1 
                    case '2' => 2 
                    case '3' => 3 
                    case '4' => 4
                    case '5' => 5 
                    case '6' => 6 
                    case '7' => 7 
                    case '8' => 8 
                    case '9' => 9
        else
            stringToNat(s[..|s|-1])*10 + stringToNat(s[|s|-1..|s|])
    }

lemma natToStringThenStringToNatIdem(n: nat)
    ensures stringToNat(natToString(n)) == n
        {}

lemma stringToNatThenNatToStringIdem(n: stringNat)
    ensures natToString(stringToNat(n)) == n
        {}

method printOpcode(seqU8: seq<u8>) returns ()
    {
        if seqU8 == [] {print("");}
        var i:= 0;
        var datasize := 0;
        while (i + 1 < |seqU8|)
            {
                if seqU8[i] == 0 {print("STOP" + "\n");}
                if seqU8[i] == 1 {print("ADD" + "\n");}
                if seqU8[i] == 2 {print("MUL" + "\n");}
                if seqU8[i] == 3 {print("SUB" + "\n");}
                if seqU8[i] == 4 {print("DIV" + "\n");}
                if seqU8[i] == 5 {print("SDIV" + "\n");}
                if seqU8[i] == 6 {print("MOD" + "\n");}
                if seqU8[i] == 7 {print("SMOD" + "\n");}
                if seqU8[i] == 8 {print("ADDMOD" + "\n");}
                if seqU8[i] == 9 {print("MULMOD" + "\n");}
                if seqU8[i] == 10 {print("EXP" + "\n");}
                if seqU8[i] == 11 {print("SIGNEXTEND" + "\n");}
                if seqU8[i] == 16 {print("LT" + "\n");}
                if seqU8[i] == 17 {print("GT" + "\n");}
                if seqU8[i] == 18 {print("SLT" + "\n");}
                if seqU8[i] == 19 {print("SGT" + "\n");}
                if seqU8[i] == 20 {print("EQ" + "\n");}
                if seqU8[i] == 21 {print("ISZERO" + "\n");}
                if seqU8[i] == 22 {print("AND" + "\n");}
                if seqU8[i] == 23 {print("EVMOR" + "\n");}
                if seqU8[i] == 24 {print("XOR" + "\n");}
                if seqU8[i] == 25 {print("NOT" + "\n");}
                if seqU8[i] == 26 {print("BYTE" + "\n");}
                if seqU8[i] == 27 {print("SHL" + "\n");}
                if seqU8[i] == 28 {print("SHR" + "\n");}
                if seqU8[i] == 29 {print("SAR" + "\n");}
                if seqU8[i] == 32 {print("SHA3" + "\n");}
                if seqU8[i] == 48 {print("ADDRESS" + "\n");}
                if seqU8[i] == 49 {print("BALANCE" + "\n");}
                if seqU8[i] == 50 {print("ORIGIN" + "\n");}
                if seqU8[i] == 51 {print("CALLER" + "\n");}
                if seqU8[i] == 52 {print("CALLVALUE" + "\n");}
                if seqU8[i] == 53 {print("CALLDATALOAD" + "\n");}
                if seqU8[i] == 54 {print("CALLDATASIZE" + "\n");}
                if seqU8[i] == 55 {print("CALLDATACOPY" + "\n");}
                if seqU8[i] == 56 {print("CODESIZE" + "\n");}
                if seqU8[i] == 57 {print("CODECOPY" + "\n");}
                if seqU8[i] == 58 {print("GASPRICE" + "\n");}
                if seqU8[i] == 59 {print("EXTCODESIZE" + "\n");}
                if seqU8[i] == 60 {print("EXTCODECOPY" + "\n");}
                if seqU8[i] == 61 {print("RETURNDATASIZE" + "\n");}
                if seqU8[i] == 62 {print("RETURNDATACOPY" + "\n");}
                if seqU8[i] == 63 {print("EXTCODEHASH" + "\n");}
                if seqU8[i] == 64 {print("BLOCKHASH" + "\n");}
                if seqU8[i] == 65 {print("COINBASE" + "\n");}
                if seqU8[i] == 66 {print("TIMESTAMP" + "\n");}
                if seqU8[i] == 67 {print("NUMBER" + "\n");}
                if seqU8[i] == 68 {print("DIFFICLUTY" + "\n");}
                if seqU8[i] == 69 {print("GASLIMIT" + "\n");}
                if seqU8[i] == 70 {print("CHAINID" + "\n");}
                if seqU8[i] == 71 {print("SELFBALANCE" + "\n");}
                if seqU8[i] == 72 {print("BASEFEE" + "\n");}
                if seqU8[i] == 80 {print("POP" + "\n");}
                if seqU8[i] == 81 {print("MLOAD" + "\n");}
                if seqU8[i] == 82 {print("MSTORE" + "\n");}
                if seqU8[i] == 83 {print("MSTORE8" + "\n");}
                if seqU8[i] == 84 {print("SLOAD" + "\n");}
                if seqU8[i] == 85 {print("SSTORE" + "\n");}
                if seqU8[i] == 86 {print("JUMP" + "\n");}
                if seqU8[i] == 87 {print("JUMPI" + "\n");}
                if seqU8[i] == 88 {print("PC" + "\n");}
                if seqU8[i] == 89 {print("MSIZE" + "\n");}
                if seqU8[i] == 90 {print("GAS" + "\n");}
                if seqU8[i] == 91 {print("JUMPDEST" + "\n");}
                if seqU8[i] == 96 
                                  {
                                    if |seqU8| < i+2 
                                        {
                                            print("invalid bytecode");
                                        }
                                    if |seqU8| >= i+2 
                                        {
                                            var data:= ReadUint8([seqU8[i+1]],0) as nat;
                                            {print("PUSH1" + natToString(data) + "\n");}
                                            datasize := datasize + 1;
                                        }
                                  }
                // if one comments out the piece of code below, Dafny's type conversion complains becomes evident //
                                  
                if seqU8[i] == 97 
                                  {
                                    if |seqU8| < i+3
                                        {
                                            print("invalid bytecode");
                                        }
                                    if |seqU8| >= i+3
                                        {
                                            var data:= ReadUint16(seqU8[i+1..i+3],0) as nat;
                                            {print("PUSH1" + natToString(data) + "\n");}
                                            datasize := datasize + 2;
                                        }
                                  }
                
                // end of the commented out part of the code //
            i := i + 1 + datasize;        
            }
        
    }

       // ----------------------------------------------------------------------------------------//                   
                           // stuff commented out below are to be added to above in near future //
       // ----------------------------------------------------------------------------------------//
/*                                 
                case 97 => if |seqU8| < 3 
                                then accum + [INVALID]
                           else 
                                var data := ReadUint16(seqU8[1..3],1);
                                convertSeqU8ToOpcode(seqU8[3..], accum + [PUSH2(data)])
                case 98 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 99 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 100 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 101 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 102 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 103 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 104 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 105 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 106 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 107 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 108 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 109 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 110 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 111 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 112 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 113 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 114 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 115 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 116 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 117 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 118 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 119 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 120 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 121 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 122 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 123 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 124 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 125 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 126 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 127 => convertSeqU8ToOpcode(seqU8[1..], accum + [])
                case 128 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP1])
                case 129 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP2])
                case 130 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP3])
                case 131 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP4])
                case 132 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP5])
                case 133 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP6])
                case 134 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP7])
                case 135 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP8])
                case 136 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP9])
                case 137 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP10])
                case 138 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP11])
                case 139 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP12])
                case 140 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP13])
                case 141 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP14])
                case 142 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP15])
                case 143 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP16])
                case 144 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP1])
                case 145 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP2])
                case 146 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP3])
                case 147 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP4])
                case 148 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP5])
                case 149 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP6])
                case 150 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP7])
                case 151 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP8])
                case 152 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP9])
                case 153 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP10])
                case 154 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP11])
                case 155 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP12])
                case 156 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP13])
                case 157 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP14])
                case 158 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP15])
                case 159 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP16])
                case 160 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG0])
                case 161 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG1])
                case 162 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG2])
                case 163 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG3])
                case 164 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG4])
                case 240 => convertSeqU8ToOpcode(seqU8[1..], accum + [CREATE])
                case 241 => convertSeqU8ToOpcode(seqU8[1..], accum + [CALL])
                case 242 => convertSeqU8ToOpcode(seqU8[1..], accum + [CALLCODE])
                case 243 => convertSeqU8ToOpcode(seqU8[1..], accum + [RETURN])
                case 244 => convertSeqU8ToOpcode(seqU8[1..], accum + [DELEGATECALL])
                case 245 => convertSeqU8ToOpcode(seqU8[1..], accum + [CREATE2])
                case 250 => convertSeqU8ToOpcode(seqU8[1..], accum + [STATICCALL])
                case 253 => convertSeqU8ToOpcode(seqU8[1..], accum + [REVERT])
                case 254 => convertSeqU8ToOpcode(seqU8[1..], accum + [INVALID])
                case 255 => convertSeqU8ToOpcode(seqU8[1..], accum + [SELFDESTRUCT])
                case _ => accum
            }
    }
*/

// ----------------------------------------------------------------------------------------------------//
//-----------------------------------------------------------------------------------------------------//
                // This area is experimental, potentially useful or certainly useless//


function method IsArith(chr:char): string {
    match chr
        case '0' => "STOP"
        case '1' => "ADD"
        case '2' => "MUL"
        case '3' => "SUB"
        case '4' => "DIV"
        case '5' => "SDIV"
        case '6' => "MOD"
        case '7' => "SMOD"
        case '8' => "ADDMOD"
        case '9' => "MULMOD"
        case 'a' => "EXP"
        case 'b' => "SIGNEXTEND"
        case _ => "INVALID"
}

function method IsLogic(chr: char): string {
    match chr
        case '0' => "LT"
        case '1' => "GT"
        case '2' => "SLT"
        case '3' => "SGT"
        case '4' => "EQ"
        case '5' => "ISZERO"
        case '6' => "AND"
        case '7' => "OR"
        case '8' => "XOR"
        case '9' => "NOT"
        case 'a' => "BYTE"
        case 'b' => "SHL"
        case 'c' => "SHR"
        case 'd' => "SAR"
        case _ => "INVALID"
}

function method IsEnvInfo(chr: char): string {
    match chr
        case '0' => "ADDRESS"
        case '1' => "BALANCE"
        case '2' => "ORIGIN"
        case '4' => "CALLVALUE"
        case '5' => "CALLDATALOAD"
        case '6' => "CALLDATASIZE"
        case '7' => "CALLDATACOPY"
        case '8' => "CODESIZE"
        case '9' => "CODECOPY"
        case 'a' => "GASPRICE"
        case 'b' => "EXTCODESIZE"
        case 'c' => "EXTCODECOPY"
        case 'd' => "RETURNDATASIZE"
        case 'e' => "RETURNDATACOPY"
        case 'f' => "EXTCODEHASH"
        case _ => "INVALID"
}

function method IsBlockInfo(chr: char): string {
    match chr 
        case '0' => "BLOCKHASH"
        case '1' => "COINBASE"
        case '2' => "TIMESTAMP"
        case '3' => "NUMBER"
        case '4' => "DIFFICULTY"
        case '5' => "GASLIMIT"
        case '6' => "CHAINID"
        case '7' => "SELFBALANCE"
        case _ => "INVALID"
}

function method IsStackMemoryFlow(chr: char): string {
    match chr
        case '0' => "POP"
        case '1' => "MLOAD"
        case '2' => "MSTORE"
        case '3' => "MSTORE8"
        case '4' => "SLOAD"
        case '5' => "SSTORE"
        case '6' => "JUMP"
        case '7' => "JUMPI"
        case '8' => "PC"
        case '9' => "MSIZE"
        case 'a' => "GAS"
        case 'b' => "JUMPDEST"
        case _ => "INVALID"
}

function method IsDup(chr: char): string {
    match chr
        case '0' => "DUP1"
        case '1' => "DUP2"
        case '2' => "DUP3"
        case '3' => "DUP4"
        case '4' => "DUP5"
        case '5' => "DUP6"
        case '6' => "DUP7"
        case '7' => "DUP8"
        case '8' => "DUP9"
        case '9' => "DUP10"
        case 'a' => "DUP11"
        case 'b' => "DUP12"
        case 'c' => "DUP13"
        case 'd' => "DUP14"
        case 'e' => "DUP15"
        case 'f' => "DUP16"
        case _ => "INVALID"

}

function method IsSwap(chr: char): string {
    match chr 
        case '0' => "SWAP1"
        case '1' => "SWAP2"
        case '2' => "SWAP3"
        case '3' => "SWAP4"
        case '4' => "SWAP5"
        case '5' => "SWAP6"
        case '6' => "SWAP7"
        case '7' => "SWAP8"
        case '8' => "SWAP9"
        case '9' => "SWAP10"
        case 'a' => "SWAP11"
        case 'b' => "SWAP12"
        case 'c' => "SWAP13"
        case 'd' => "SWAP14"
        case 'e' => "SWAP15"
        case 'f' => "SWAP16"
        case _ => "INVALID"
}

function method IsLog(chr: char): string {
    match chr 
        case '0' => "LOG0"
        case '1' => "LOG1"
        case '2' => "LOG2"
        case '3' => "LOG3"
        case '4' => "LOG4"
        case _ => "INVALID"
}

function method IsSysCall(chr:char): string {
    match chr
        case '0' => "CREATE"
        case '1' => "CALL"
        case '2' => "CALLCODE"
        case '3' => "RETURN"
        case '4' => "DELEGATECALL"
        case '5' => "CREATE2"
        case 'a' => "STATICCALL"
        case 'd' => "REVERT"
        case 'e' => "INVALID"
        case 'f' => "SELFDESTRUCT"
        case _ => "INVALID"
}

function method IsKec(chr: char): string {
    match chr
        case '0' => "KECCAK256"
        case _ => "INVALID"
}

function method IsEndOfFile(chr: char): string {
    match chr
        case 'f' => "EOF"
        case _ => "INVALID"

}

function method IsPushUpTo16(chr: char): (string, nat) {
    match chr 
        case '0' => ("PUSH1", 1 * 2)
        case '1' => ("PUSH2", 2 * 2)
        case '2' => ("PUSH3", 3 * 2)
        case '3' => ("PUSH4", 4 * 2)
        case '4' => ("PUSH5", 5 * 2)
        case '5' => ("PUSH6", 6 * 2)
        case '6' => ("PUSH7", 7 * 2)
        case '7' => ("PUSH8", 8 * 2)
        case '8' => ("PUSH9", 9 * 2)
        case '9' => ("PUSH10", 10 * 2)
        case 'a' => ("PUSH11", 11 * 2)
        case 'b' => ("PUSH12", 12 * 2)
        case 'c' => ("PUSH13", 13 * 2)
        case 'd' => ("PUSH14", 14 * 2)
        case 'e' => ("PUSH15", 15 * 2)
        case 'f' => ("PUSH16", 16 * 2)
        case _ => ("INVALID", 0)
}

function method IsPushMoreThan16(chr: char): (string, nat) {
    match chr 
        case '0' => ("PUSH17", 17)
        case '1' => ("PUSH18", 18)
        case '2' => ("PUSH19", 19)
        case '3' => ("PUSH20", 20)
        case '4' => ("PUSH21", 21)
        case '5' => ("PUSH22", 22)
        case '6' => ("PUSH23", 23)
        case '7' => ("PUSH24", 24)
        case '8' => ("PUSH25", 25)
        case '9' => ("PUSH26", 26)
        case 'a' => ("PUSH27", 27)
        case 'b' => ("PUSH28", 28)
        case 'c' => ("PUSH29", 29)
        case 'd' => ("PUSH30", 30)
        case 'e' => ("PUSH31", 31)
        case 'f' => ("PUSH32", 32)
        case _ => ("INVALID", 0)
}

function method disassembleOneInstr(str: string): string 
    requires |str| == 2 {
        var str0 := str[0];
        var str1 := str[1];
        match str0
            case '0' => IsArith(str1)
            case '1' => IsLogic(str1)
            case '2' => IsKec(str1)
            case '3' => IsEnvInfo(str1)
            case '4' => IsBlockInfo(str1)
            case '5' => IsStackMemoryFlow(str1)
            case '6' => IsPushUpTo16(str1).0
            case '7' => IsPushMoreThan16(str1).0
            case '8' => IsDup(str1)
            case '9' => IsSwap(str1)
            case 'a' => IsLog(str1)
            case 'e' => IsEndOfFile(str1)
            case 'f' => IsSysCall(str1)
            case _ => "INVALID"
}

//this is not good given Dafny has issues with recursion and chunking a sequence in function calls.
//it has to be rewritten to avoid use of take or drop.
function method implode(str: seq<char>, acc: string): string 
   {
        if str == []
            then    
                acc
        else 
            implode(str[1..], acc + [str[0]])
}

method Implode(str: seq<char>) returns (s: string)
    {
    var i := 0;
    var tempo := "";
    while (|str| != 0 && i < |str|)
        decreases |str| - i
        invariant |tempo| == i
        invariant i <= |str|
        invariant (forall k: nat:: 0 <= k < i && str[k] in str[..i] ==> str[k] in tempo)
        {
            tempo:= tempo + [str[i]];
            i:= i + 1;
        }
    assert |tempo| == |str|;
    return (tempo);
    assert tempo == str;
}

function method disassmAllInstr(str: string, counter: nat, accumulator: seq<string>): seq<string>  
    decreases |str| - counter
    {
        if |str| <= counter + 1
            then
                accumulator
        else
            var str0 := str[counter];
            var str1 := str[counter + 1];
            match str0
                case '0' => 
                    var disassemOne:= IsArith(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '1' => 
                    var disassemOne:= IsLogic(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '2' => 
                    var disassemOne:= IsKec(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '3' => 
                    var disassemOne:= IsEnvInfo(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '4' => 
                    var disassemOne:= IsBlockInfo(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '5' => 
                    var disassemOne:= IsStackMemoryFlow(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '6' => 
                    var (disassemOne, width):= IsPushUpTo16(str1);
                    if disassemOne == "INVALID" 
                        then disassmAllInstr(str, counter + 2, accumulator + ["INVALID"])
                    else 
                        var newCounter:= counter + 2 ;
                        if |str| < newCounter + width - 1
                            then
                                disassmAllInstr(str, newCounter, accumulator + ["INVALID"])
                        else
                        var pushData:= str[newCounter..(newCounter + width - 1)];
                            disassmAllInstr(str, newCounter + width, accumulator + [disassemOne] + [pushData])
                case '7' => disassmAllInstr(str, counter + 2, accumulator + ["INVALID"])
                case '8' => 
                    var disassemOne:= IsDup(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '9' => 
                    var disassemOne:= IsSwap(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case 'a' => 
                    var disassemOne:= IsLog(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case 'e' => 
                    var disassemOne:= IsEndOfFile(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case 'f' => 
                    var disassemOne:= IsSysCall(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case _ => disassmAllInstr(str, counter + 2, accumulator + ["INVALID"])
            

}

/*
function method disassmAllInstr_seqVer(str: seq<char>, counter: nat, accumulator: seq<u8>): seq<u8> 
    decreases |str| - counter
    {
        if |str| <= counter + 1
            then
                accumulator
        else
            var str0 := str[counter];
            var str1 := str[counter + 1];
            match str0
                case '0' => 
                    var disassemOne:= IsArith(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '1' => 
                    var disassemOne:= IsLogic(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '2' => 
                    var disassemOne:= IsKec(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '3' => 
                    var disassemOne:= IsEnvInfo(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '4' => 
                    var disassemOne:= IsBlockInfo(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '5' => 
                    var disassemOne:= IsStackMemoryFlow(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '6' => disassmAllInstr(str, counter + 2, accumulator + [INVALID])
                case '7' => disassmAllInstr(str, counter + 2, accumulator + [INVALID])
                case '8' => 
                    var disassemOne:= IsDup(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case '9' => 
                    var disassemOne:= IsSwap(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case 'a' => 
                    var disassemOne:= IsLog(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case 'e' => 
                    var disassemOne:= IsEndOfFile(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case 'f' => 
                    var disassemOne:= IsSysCall(str1);
                    disassmAllInstr(str, counter + 2, accumulator + [disassemOne])
                case _ => disassmAllInstr(str, counter + 2, accumulator + [INVALID])
}

*/

datatype Opcodes =
// 0s: Stop and Arithmetic Operations
      STOP 
	 |ADD 
	 |MUL 
	 |SUB 
	 |DIV 
	 |SDIV 
	 |MOD 
	 |SMOD 
	 |ADDMOD 
	 |MULMOD 
	 |EXP 
	 |SIGNEXTEND 
	// 10s: Comparison & Bitwise Logic Operations
	 |LT 
	 |GT 
	 |SLT 
	 |SGT 
	 |EQ 
	 |ISZERO 
	 |AND 
	 |OR 
	 |XOR 
	 |NOT 
	 |BYTE 
	 |SHL 
     |SHR 
     |SAR 
	// 20s: SHA3
	 |KECCAK256 
	// 30s: Environment Information
	 |ADDRESS 
	 |BALANCE 
	 |ORIGIN 
	 |CALLER 
	 |CALLVALUE 
	 |CALLDATALOAD 
	 |CALLDATASIZE 
	 |CALLDATACOPY 
	 |CODESIZE 
	 |CODECOPY 
	 |GASPRICE 
	 |EXTCODESIZE 
	 |EXTCODECOPY 
	 |RETURNDATASIZE 
	 |RETURNDATACOPY 
     |EXTCODEHASH 
	// 40s: Block Information
	 |BLOCKHASH 
	 |COINBASE 
	 |TIMESTAMP 
	 |NUMBER 
	 |DIFFICULTY 
	 |GASLIMIT 
     |CHAINID 
     |SELFBALANCE 
	// 50s: Stack, Memory Storage and Flow Operations
	 |POP
	 |MLOAD 
	 |MSTORE 
	 |MSTORE8
	 |SLOAD
	 |SSTORE 
	 |JUMP 
	 |JUMPI 
	 |PC 
	 |MSIZE 
	 |GAS 
	 |JUMPDEST 
	// 60s & 70s: Push Operations
     |PUSH1(d1: Int.u8)
     |PUSH2(d2: Int.u16)
     |PUSH3(d3: Int.u24)
     |PUSH4(d4: Int.u32)
     |PUSH5(d5: Int.u40)
     |PUSH6(d6: Int.u48)
     |PUSH7(d7: Int.u56)
     |PUSH8(d8: Int.u64)
     /*
     |PUSH9(d9: Int.u72)
     |PUSH1(d1: Int.u8)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH1(d1: Int.u8)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH1(d1: Int.u8)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
     |PUSH2(d2: Int.u16)
	 |PUSH (n: nat, u :u256) 
     */
	// 80s: Duplication Operations
	 |DUP1 
	 |DUP2 
	 |DUP3
	 |DUP4 
	 |DUP5 
	 |DUP6 
	 |DUP7 
	 |DUP8 
	 |DUP9 
	 |DUP10 
	 |DUP11 
	 |DUP12 
	 |DUP13 
	 |DUP14 
	 |DUP15
	 |DUP16 
	// 90s: Exchange Operations
	 |SWAP1 
	 |SWAP2 
	 |SWAP3 
	 |SWAP4 
	 |SWAP5 
	 |SWAP6 
	 |SWAP7 
	 |SWAP8 
	 |SWAP9 
	 |SWAP10 
	 |SWAP11 
	 |SWAP12 
	 |SWAP13 
	 |SWAP14 
	 |SWAP15 
	 |SWAP16 
	// a0s: Logging Operations
	 |LOG0 
	 |LOG1 
	 |LOG2 
	 |LOG3 
	 |LOG4 
    // e0s
     |EOF 
	// f0s: System operations
	 |CREATE 
	 |CALL 
	 |CALLCODE 
	 |RETURN 
	 |DELEGATECALL 
     |CREATE2 
	 |STATICCALL 
	 |REVERT 
	 |INVALID
     |SELFDESTRUCT

function method convertSeqU8ToOpcode(seqU8: seq<Int.u8>, accum: seq<Opcodes>) : seq<Opcodes>
    {
        if seqU8 == []
            then accum
        else
            match seqU8[0]
                case 0 => convertSeqU8ToOpcode(seqU8[1..], accum + [STOP])
                case 1 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 2 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 3 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 4 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 5 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 6 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 7 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 8 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 9 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 10 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 11 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 16 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 17 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 18 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 19 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 20 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 21 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 22 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 23 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 24 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 25 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 26 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 27 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 28 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 29 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 32 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 48 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 49 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 50 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 51 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 52 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 53 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 54 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 55 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 56 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 57 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 58 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 59 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 60 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 61 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 62 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 63 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 64 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 65 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 66 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 67 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 68 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 69 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 70 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])

                case 71 => convertSeqU8ToOpcode(seqU8[1..], accum + [STOP])
                case 72 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 73 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 74 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 75 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 76 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 77 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 78 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 79 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 80 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 81 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 82 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 83 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 84 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 85 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 86 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 87 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 88 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 89 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 90 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 91 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 92 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 93 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 94 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 95 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 96 => if |seqU8| < 2 
                                then accum + [INVALID]
                           else 
                                var data:= ReadUint8([seqU8[1]],0); 
                                convertSeqU8ToOpcode(seqU8[2..], accum + [PUSH1(data)])
                case 97 => if |seqU8| < 3 
                                then accum + [INVALID]
                           else 
                                var data := ReadUint16(seqU8[1..3],1);
                                convertSeqU8ToOpcode(seqU8[3..], accum + [PUSH2(data)])
                case 98 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 99 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 100 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 101 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 102 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 103 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 104 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 105 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 106 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 107 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 108 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 109 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 110 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 111 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 112 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 113 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 114 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 115 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 116 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 117 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 118 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 119 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 120 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 121 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 122 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 123 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 124 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 125 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 126 => convertSeqU8ToOpcode(seqU8[1..], accum + [ADD])
                case 127 => convertSeqU8ToOpcode(seqU8[1..], accum + [])
                case 128 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP1])
                case 129 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP2])
                case 130 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP3])
                case 131 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP4])
                case 132 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP5])
                case 133 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP6])
                case 134 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP7])
                case 135 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP8])
                case 136 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP9])
                case 137 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP10])
                case 138 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP11])
                case 139 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP12])
                case 140 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP13])
                case 141 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP14])
                case 142 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP15])
                case 143 => convertSeqU8ToOpcode(seqU8[1..], accum + [DUP16])
                case 144 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP1])
                case 145 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP2])
                case 146 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP3])
                case 147 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP4])
                case 148 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP5])
                case 149 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP6])
                case 150 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP7])
                case 151 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP8])
                case 152 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP9])
                case 153 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP10])
                case 154 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP11])
                case 155 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP12])
                case 156 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP13])
                case 157 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP14])
                case 158 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP15])
                case 159 => convertSeqU8ToOpcode(seqU8[1..], accum + [SWAP16])
                case 160 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG0])
                case 161 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG1])
                case 162 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG2])
                case 163 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG3])
                case 164 => convertSeqU8ToOpcode(seqU8[1..], accum + [LOG4])
                case 240 => convertSeqU8ToOpcode(seqU8[1..], accum + [CREATE])
                case 241 => convertSeqU8ToOpcode(seqU8[1..], accum + [CALL])
                case 242 => convertSeqU8ToOpcode(seqU8[1..], accum + [CALLCODE])
                case 243 => convertSeqU8ToOpcode(seqU8[1..], accum + [RETURN])
                case 244 => convertSeqU8ToOpcode(seqU8[1..], accum + [DELEGATECALL])
                case 245 => convertSeqU8ToOpcode(seqU8[1..], accum + [CREATE2])
                case 250 => convertSeqU8ToOpcode(seqU8[1..], accum + [STATICCALL])
                case 253 => convertSeqU8ToOpcode(seqU8[1..], accum + [REVERT])
                case 254 => convertSeqU8ToOpcode(seqU8[1..], accum + [INVALID])
                case 255 => convertSeqU8ToOpcode(seqU8[1..], accum + [SELFDESTRUCT])
                case _ => accum
    }

// --------------------------------------------------------------------------------------------//
// --------------------------------------------------------------------------------------------//
                    // end of the experimanetal area //