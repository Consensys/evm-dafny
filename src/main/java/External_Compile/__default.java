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
package External_Compile;

import java.math.BigInteger;
import java.util.Arrays;

import dafny.DafnySequence;

/**
 * Provides concrete implementations for all methods defined as
 * <code>{:extern}</code> within the DafnyEVM.
 *
 * @author David J. Pearce
 *
 */
public class __default {
    /**
     * Initialise the bundle with our default implementations.
     */
    public static PrecompileBundle bundle = new PrecompileBundle();

    /**
     * This provides a default set of implementations which is not intended to be
     * used in practice, but is required when compiling the Dafny generated source
     * code. This is really an artifact of the way that Dafny generates code, for
     * which there are currently no easy work arounds.
     *
     * @author David J. Pearce
     *
     */
    public static class PrecompileBundle {
        public byte[] ECDSARecover(byte[] h, byte v, BigInteger r, BigInteger s) {
            return new byte[0];
        }

        public BigInteger sha3(byte[] bytes) {
            // A very poor mans implementation of sha3 :)
            return BigInteger.valueOf(Arrays.hashCode(bytes));
        }

        public byte[] sha256(byte[] bytes) {
            // A very poor mans implementation of sha256 :)
            return new byte[0];
        }

        public byte[] ripEmd160(byte[] bytes) {
            return new byte[0];
        }

        public byte[] modExp(byte[] B, byte[] E, byte[] M) {
            return new byte[0];
        }
        public byte[] blake2f(byte[] bytes) {
            return new byte[0];
        }
    }

    @SuppressWarnings({"unchecked","rawtypes"})
    public static DafnySequence<Byte> ECDSARecover(DafnySequence<? extends Byte> _h, byte v, BigInteger r, BigInteger s) {
        byte[] h = DafnySequence.toByteArray((DafnySequence) _h);
        return DafnySequence.fromBytes(bundle.ECDSARecover(h, v, r, s));
    }

    @SuppressWarnings({"unchecked","rawtypes"})
    public static BigInteger sha3(DafnySequence<? extends Byte> bytes) {
        return bundle.sha3(DafnySequence.toByteArray((DafnySequence) bytes));
    }

    @SuppressWarnings({"unchecked","rawtypes"})
    public static DafnySequence<Byte> sha256(DafnySequence<? extends Byte> bytes) {
        byte[] hash = bundle.sha256(DafnySequence.toByteArray((DafnySequence) bytes));
        return DafnySequence.fromBytes(hash);
    }

    @SuppressWarnings({"unchecked","rawtypes"})
    public static DafnySequence<Byte> ripEmd160(DafnySequence<? extends Byte> bytes) {
        byte[] tmp = bundle.ripEmd160(DafnySequence.toByteArray((DafnySequence) bytes));
        return DafnySequence.fromBytes(tmp);
    }

    @SuppressWarnings({"unchecked","rawtypes"})
    public static DafnySequence<? extends Byte> modExp(DafnySequence<? extends Byte> _B,
            DafnySequence<? extends Byte> _E, DafnySequence<? extends Byte> _M) {
        byte[] B = DafnySequence.toByteArray((DafnySequence) _B);
        byte[] E = DafnySequence.toByteArray((DafnySequence) _E);
        byte[] M = DafnySequence.toByteArray((DafnySequence) _M);
        return DafnySequence.fromBytes(bundle.modExp(B,E,M));
    }

    public static DafnySequence<Byte> blake2f(DafnySequence<? extends Byte> _bytes) {
        @SuppressWarnings({"unchecked","rawtypes"})
        byte[] bytes = DafnySequence.toByteArray((DafnySequence) _bytes);
        return DafnySequence.fromBytes(bundle.blake2f(bytes));
    }
}
