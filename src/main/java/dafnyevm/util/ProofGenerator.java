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
import java.util.Arrays;

import evmtools.util.Bytecodes;

public class ProofGenerator {
    /**
     * Contains the contract bytecode for which we are generating a proof.
     */
    private final byte[] bytes;

    public ProofGenerator(byte[] bytes) {
        this.bytes = bytes;
    }

    public void print() {
        boolean[] insns = determineInstructionBoundaries(bytes);
        // NOTE: this is a really a very simple hack for now.
        System.out.println("include \"../../dafny/evm.dfy\"");
        System.out.println("include \"../../dafny/evms/berlin.dfy\"");
        System.out.println("import opened Int");
        System.out.println("import opened Opcode");
        System.out.println("import opened Memory");
        System.out.println("import opened Bytecode");
        System.out.println("import opened EvmBerlin");
        System.out.println("import opened EvmState");
        System.out.println();
        System.out.println("const BYTECODE : seq<u8> := " + toBytecodeString(bytes,insns) + ";");
        System.out.println();
        System.out.println("method main(context: Context.T, world: map<u160,WorldState.Account>, gas: nat)");
        System.out.println("requires context.writePermission");
        System.out.println("requires gas > 100000");
        System.out.println("requires context.address in world {");
        System.out.println("\tvar st := EvmBerlin.Create(context,world,gas,BYTECODE);");
        BigInteger top = null;
        for(int pc=0;pc<bytes.length;++pc) {
            int opcode = bytes[pc] & 0xff;
            if(opcode >= PUSH1 && opcode <= PUSH32) {
                int len = (opcode - PUSH1) + 1;
                BigInteger operand = new BigInteger(1,Arrays.copyOfRange(bytes,pc+1,pc+1+len));
                if(opcode >= PUSH1 && opcode <= PUSH8) {
                    System.out.println("\tst := " + toOpcodeName(opcode) + "(st, 0x" + operand.toString(16) + ");");
                } else {
                    System.out.println("\tst := PushN(st, " + len + ", 0x" + operand.toString(16) + ");");
                }
                pc += len;
                top = operand;
            } else if(opcode == JUMPDEST) {
                System.out.println("}");
                System.out.println();
                System.out.println("method block_0x" + Integer.toHexString(pc) + "(st': State)");
                System.out.println("requires st'.OK? && st'.PC() == 0x" + Integer.toHexString(pc));
                System.out.println("requires st'.evm.code == Code.Create(BYTECODE)");
                System.out.println("requires st'.WritesPermitted()");
                System.out.println("requires st'.Operands() >= 0 && st'.Capacity() > 0 {");
                System.out.println("\tvar st := JumpDest(st');");

            } else if(opcode == JUMP) {
                if(top == null) {
                    throw new IllegalArgumentException("Cannot reason about branch");
                }
                System.out.println("\tst := " + toOpcodeName(opcode) + "(st);");
                System.out.println("\tblock_0x" + top.toString(16) + "(st);");
                top = null;
            } else if(opcode == JUMPI) {
                if(top == null) {
                    throw new IllegalArgumentException("Cannot reason about branch");
                }
                String v = "tmp" + pc;
                System.out.println("\tvar " + v + " := st.Peek(1);");
                System.out.println("\tst := " + toOpcodeName(opcode) + "(st);");
                System.out.println("\tif " + v + " != 0 { block_0x" + top.toString(16) + "(st); return; }");

                top = null;
            } else if(opcode >= DUP1 && opcode <= DUP16) {
                int k = (opcode - DUP1) + 1;
                System.out.println("\tst := Dup(st," + k + ");");
            } else if(opcode >= SWAP1 && opcode <= SWAP16) {
                int k = (opcode - SWAP1) + 1;
                System.out.println("\tst := Swap(st," + k + ");");
            } else {
                System.out.println("\tst := " + toOpcodeName(opcode) + "(st);");
                top = null;
            }
        }
        System.out.println("}");
    }

    private static String toOpcodeName(int opcode) {
        return opcodes[opcode];
    }

    private static String toBytecodeString(byte[] bytes, boolean[] insns) {
        StringBuffer r = new StringBuffer();
        r.append("[");
        for(int i=0;i!=bytes.length;++i) {
            int len = 0;
            int opcode = bytes[i] & 0xff;
            if(i!=0) { r.append("\t"); }
            r.append(Bytecodes.toString(bytes[i]&0xff));
            if((i+1) != bytes.length) { r.append(", "); }
            if(opcode >= PUSH1 && opcode <= PUSH32) {
                len = (opcode - PUSH1) + 1;
                for (int j = 0; j != len; ++j) {
                    r.append("0x" + Integer.toHexString(bytes[i+j+1] & 0xff));
                    r.append(",");
                }
            }
            r.append(" // 0x");
            r.append(Integer.toHexString(i));
            r.append("\n");
            i += len;
        }
        r.append("]");
        return r.toString();
    }

    private static boolean[] determineInstructionBoundaries(byte[] bytes) {
        boolean[] boundaries = new boolean[bytes.length];
        for(int i=0;i!=bytes.length;++i) {
            int opcode = bytes[i] & 0xff;
            boundaries[i] = true;
            if (opcode >= PUSH1 && opcode <= PUSH32) {
                int len = (opcode - PUSH1) + 1;
                i += len;
            }
        }
        return boundaries;
    }

    // 0s: Stop and Arithmetic Operations
    public static final int STOP = 0x0;
    public static final int ADD = 0x01;
    public static final int MUL = 0x02;
    public static final int SUB = 0x03;
    public static final int DIV = 0x04;
    public static final int SDIV = 0x05;
    public static final int MOD = 0x06;
    public static final int SMOD = 0x07;
    public static final int ADDMOD = 0x08;
    public static final int MULMOD = 0x09;
    public static final int EXP = 0x0a;
    public static final int SIGNEXTEND = 0x0b;
    // 10s: Comparison & Bitwise Logic Operations
    public static final int LT = 0x10;
    public static final int GT = 0x11;
    public static final int SLT = 0x12;
    public static final int SGT = 0x13;
    public static final int EQ = 0x14;
    public static final int ISZERO = 0x15;
    public static final int AND = 0x16;
    public static final int OR = 0x17;
    public static final int XOR = 0x18;
    public static final int NOT = 0x19;
    public static final int BYTE = 0x1a;
    public static final int SHL = 0x1b;
    public static final int SHR = 0x1c;
    public static final int SAR = 0x1d;
    // 20s: SHA3
    public static final int KECCAK256 = 0x20;
    // 30s: Environment Information
    public static final int ADDRESS = 0x30;
    public static final int BALANCE = 0x31;
    public static final int ORIGIN = 0x32;
    public static final int CALLER = 0x33;
    public static final int CALLVALUE = 0x34;
    public static final int CALLDATALOAD = 0x35;
    public static final int CALLDATASIZE = 0x36;
    public static final int CALLDATACOPY = 0x37;
    public static final int CODESIZE = 0x38;
    public static final int CODECOPY = 0x39;
    public static final int GASPRICE = 0x3a;
    public static final int EXTCODESIZE = 0x3b;
    public static final int EXTCODECOPY = 0x3c;
    public static final int RETURNDATASIZE = 0x3d;
    public static final int RETURNDATACOPY = 0x3e;
    public static final int EXTCODEHASH = 0x3f;
    // 40s: Block Information
    public static final int BLOCKHASH = 0x40;
    public static final int COINBASE = 0x41;
    public static final int TIMESTAMP = 0x42;
    public static final int NUMBER = 0x43;
    public static final int DIFFICULTY = 0x44;
    public static final int GASLIMIT = 0x45;
    public static final int CHAINID = 0x46;
    public static final int SELFBALANCE = 0x47;
    // 50s: Stack, Memory Storage and Flow Operations
    public static final int POP = 0x50;
    public static final int MLOAD = 0x51;
    public static final int MSTORE = 0x52;
    public static final int MSTORE8 = 0x53;
    public static final int SLOAD = 0x54;
    public static final int SSTORE = 0x55;
    public static final int JUMP = 0x56;
    public static final int JUMPI = 0x57;
    public static final int PC = 0x58;
    public static final int MSIZE = 0x59;
    public static final int GAS = 0x5a;
    public static final int JUMPDEST = 0x5b;
    // 60s & 70s: Push Operations
    public static final int PUSH1 = 0x60;
    public static final int PUSH2 = 0x61;
    public static final int PUSH3 = 0x62;
    public static final int PUSH4 = 0x63;
    public static final int PUSH5 = 0x64;
    public static final int PUSH6 = 0x65;
    public static final int PUSH7 = 0x66;
    public static final int PUSH8 = 0x67;
    public static final int PUSH9 = 0x68;
    public static final int PUSH10 = 0x69;
    public static final int PUSH11 = 0x6a;
    public static final int PUSH12 = 0x6b;
    public static final int PUSH13 = 0x6c;
    public static final int PUSH14 = 0x6d;
    public static final int PUSH15 = 0x6e;
    public static final int PUSH16 = 0x6f;
    public static final int PUSH17 = 0x70;
    public static final int PUSH18 = 0x71;
    public static final int PUSH19 = 0x72;
    public static final int PUSH20 = 0x73;
    public static final int PUSH21 = 0x74;
    public static final int PUSH22 = 0x75;
    public static final int PUSH23 = 0x76;
    public static final int PUSH24 = 0x77;
    public static final int PUSH25 = 0x78;
    public static final int PUSH26 = 0x79;
    public static final int PUSH27 = 0x7a;
    public static final int PUSH28 = 0x7b;
    public static final int PUSH29 = 0x7c;
    public static final int PUSH30 = 0x7d;
    public static final int PUSH31 = 0x7e;
    public static final int PUSH32 = 0x7f;
    // 80s: Duplication Operations
    public static final int DUP1 = 0x80;
    public static final int DUP2 = 0x81;
    public static final int DUP3 = 0x82;
    public static final int DUP4 = 0x83;
    public static final int DUP5 = 0x84;
    public static final int DUP6 = 0x85;
    public static final int DUP7 = 0x86;
    public static final int DUP8 = 0x87;
    public static final int DUP9 = 0x88;
    public static final int DUP10 = 0x89;
    public static final int DUP11 = 0x8a;
    public static final int DUP12 = 0x8b;
    public static final int DUP13 = 0x8c;
    public static final int DUP14 = 0x8d;
    public static final int DUP15 = 0x8e;
    public static final int DUP16 = 0x8f;
    // 90s: Exchange Operations
    public static final int SWAP1 = 0x90;
    public static final int SWAP2 = 0x91;
    public static final int SWAP3 = 0x92;
    public static final int SWAP4 = 0x93;
    public static final int SWAP5 = 0x94;
    public static final int SWAP6 = 0x95;
    public static final int SWAP7 = 0x96;
    public static final int SWAP8 = 0x97;
    public static final int SWAP9 = 0x98;
    public static final int SWAP10 = 0x99;
    public static final int SWAP11 = 0x9a;
    public static final int SWAP12 = 0x9b;
    public static final int SWAP13 = 0x9c;
    public static final int SWAP14 = 0x9d;
    public static final int SWAP15 = 0x9e;
    public static final int SWAP16 = 0x9f;
    // a0s: Logging Operations
    public static final int LOG0 = 0xa0;
    public static final int LOG1 = 0xa1;
    public static final int LOG2 = 0xa2;
    public static final int LOG3 = 0xa3;
    public static final int LOG4 = 0xa4;
    // f0s: System operations
    public static final int CREATE = 0xf0;
    public static final int CALL = 0xf1;
    public static final int CALLCODE = 0xf2;
    public static final int RETURN = 0xf3;
    public static final int DELEGATECALL = 0xf4;
    public static final int CREATE2 = 0xf5;
    public static final int STATICCALL = 0xfa;
    public static final int REVERT = 0xfd;
    public static final int INVALID = 0xfe;
    public static final int SELFDESTRUCT = 0xff;

    private static final String[] opcodes;

    /**
     * These strings have to match what's in the Bytecode.dfy file.
     */
    static {
        opcodes = new String[256];
        opcodes[STOP] = "Stop";
        opcodes[ADD] = "Add";
        opcodes[MUL] = "Mul";
        opcodes[SUB] = "Sub";
        opcodes[DIV] = "Div";
        opcodes[SDIV] = "SDiv";
        opcodes[MOD] = "Mod";
        opcodes[SMOD] = "SMod";
        opcodes[ADDMOD] = "AddMod";
        opcodes[MULMOD] = "MulMod";
        opcodes[EXP] = "Exp";
        opcodes[SIGNEXTEND] = "SignExtend";
        // 10s: Comparison & Bitwise Logic Operations
        opcodes[LT] = "Lt";
        opcodes[GT] = "Gt";
        opcodes[SLT] = "SLt";
        opcodes[SGT] = "SGt";
        opcodes[EQ] = "Eq";
        opcodes[ISZERO] = "IsZero";
        opcodes[AND] = "And";
        opcodes[OR] = "Or";
        opcodes[XOR] = "Xor";
        opcodes[NOT] = "Not";
        opcodes[BYTE] = "Byte";
        opcodes[SHL] = "Shl";
        opcodes[SHR] = "Shr";
        opcodes[SAR] = "Sar";
        // 20s: SHA3
        opcodes[KECCAK256] = "Keccak256";
        // 30s: Environment Information
        opcodes[ADDRESS] = "Address";
        opcodes[BALANCE] = "Balance";
        opcodes[ORIGIN] = "Origin";
        opcodes[CALLER] = "Caller";
        opcodes[CALLVALUE] = "CallValue";
        opcodes[CALLDATALOAD] = "CallDataLoad";
        opcodes[CALLDATASIZE] = "CallDataSize";
        opcodes[CALLDATACOPY] = "CallDataCopy";
        opcodes[CODESIZE] = "CodeSize";
        opcodes[CODECOPY] = "CodeCopy";
        opcodes[GASPRICE] = "GasPrice";
        opcodes[EXTCODESIZE] = "ExtCodeSize";
        opcodes[EXTCODECOPY] = "ExtCodeCopy";
        opcodes[RETURNDATASIZE] = "ReturnDataSize";
        opcodes[RETURNDATACOPY] = "ReturnDataCopy";
        opcodes[EXTCODEHASH] = "ExtCodeHash";
        // 40s: Block Information
        opcodes[BLOCKHASH] = "BlockHash";
        opcodes[COINBASE] = "CoinBase";
        opcodes[TIMESTAMP] = "TimeStamp";
        opcodes[NUMBER] = "Number";
        opcodes[DIFFICULTY] = "Difficulty";
        opcodes[GASLIMIT] = "GasLimit";
        opcodes[CHAINID] = "ChainID";
        opcodes[SELFBALANCE] = "SelfBalance";
        // 50s: Stack, Memory Storage and Flow Operations
        opcodes[POP] = "Pop";
        opcodes[MLOAD] = "MLoad";
        opcodes[MSTORE] = "MStore";
        opcodes[MSTORE8] = "MStore8";
        opcodes[SLOAD] = "SLoad";
        opcodes[SSTORE] = "SStore";
        opcodes[JUMP] = "Jump";
        opcodes[JUMPI] = "JumpI";
        opcodes[PC] = "Pc";
        opcodes[MSIZE] = "MSize";
        opcodes[GAS] = "Gas";
        opcodes[JUMPDEST] = "JumpDest";
        // 60s & 70s: Push Operations
        opcodes[PUSH1] = "Push1";
        opcodes[PUSH2] = "Push2";
        opcodes[PUSH3] = "Push3";
        opcodes[PUSH4] = "Push4";
        opcodes[PUSH5] = "Push5";
        opcodes[PUSH6] = "Push6";
        opcodes[PUSH7] = "Push7";
        opcodes[PUSH8] = "Push8";
        opcodes[PUSH9] = "Push9";
        opcodes[PUSH10] = "Push10";
        opcodes[PUSH11] = "Push11";
        opcodes[PUSH12] = "Push12";
        opcodes[PUSH13] = "Push13";
        opcodes[PUSH14] = "Push14";
        opcodes[PUSH15] = "Push15";
        opcodes[PUSH16] = "Push16";
        opcodes[PUSH17] = "Push17";
        opcodes[PUSH18] = "Push18";
        opcodes[PUSH19] = "Push19";
        opcodes[PUSH20] = "Push20";
        opcodes[PUSH21] = "Push21";
        opcodes[PUSH22] = "Push22";
        opcodes[PUSH23] = "Push23";
        opcodes[PUSH24] = "Push24";
        opcodes[PUSH25] = "Push25";
        opcodes[PUSH26] = "Push26";
        opcodes[PUSH27] = "Push27";
        opcodes[PUSH28] = "Push28";
        opcodes[PUSH29] = "Push29";
        opcodes[PUSH30] = "Push30";
        opcodes[PUSH31] = "Push31";
        opcodes[PUSH32] = "Push32";
        // 80s: Duplication Operations
        opcodes[DUP1] = "Dup1";
        opcodes[DUP2] = "Dup2";
        opcodes[DUP3] = "Dup3";
        opcodes[DUP4] = "Dup4";
        opcodes[DUP5] = "Dup5";
        opcodes[DUP6] = "Dup6";
        opcodes[DUP7] = "Dup7";
        opcodes[DUP8] = "Dup8";
        opcodes[DUP9] = "Dup9";
        opcodes[DUP10] = "Dup10";
        opcodes[DUP11] = "Dup11";
        opcodes[DUP12] = "Dup12";
        opcodes[DUP13] = "Dup13";
        opcodes[DUP14] = "Dup14";
        opcodes[DUP15] = "Dup15";
        opcodes[DUP16] = "Dup16";
        // 90s: Exchange Operations
        opcodes[SWAP1] = "Swap1";
        opcodes[SWAP2] = "Swap2";
        opcodes[SWAP3] = "Swap3";
        opcodes[SWAP4] = "Swap4";
        opcodes[SWAP5] = "Swap5";
        opcodes[SWAP6] = "Swap6";
        opcodes[SWAP7] = "Swap7";
        opcodes[SWAP8] = "Swap8";
        opcodes[SWAP9] = "Swap9";
        opcodes[SWAP10] = "Swap10";
        opcodes[SWAP11] = "Swap11";
        opcodes[SWAP12] = "Swap12";
        opcodes[SWAP13] = "Swap13";
        opcodes[SWAP14] = "Swap14";
        opcodes[SWAP15] = "Swap15";
        opcodes[SWAP16] = "Swap16";
        // a0s: Logging Operations
        opcodes[LOG0] = "Log0";
        opcodes[LOG1] = "Log1";
        opcodes[LOG2] = "Log2";
        opcodes[LOG3] = "Log3";
        opcodes[LOG4] = "Log4";
        // f0s: System operations
        opcodes[CREATE] = "Create";
        opcodes[CALL] = "Call";
        opcodes[CALLCODE] = "CallCode";
        opcodes[RETURN] = "Return";
        opcodes[DELEGATECALL] = "DelegateCall";
        opcodes[CREATE2] = "Create2";
        opcodes[STATICCALL] = "StaticCall";
        opcodes[REVERT] = "Revert";
        opcodes[INVALID] = "Invalid";
        opcodes[SELFDESTRUCT] = "SelfDestruct";
    }
}
