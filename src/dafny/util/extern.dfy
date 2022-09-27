
include "int.dfy"

module External {
    import opened Int
    /**
     * Compute the SHA3 (a.k.a KECCAK256) hash of a sequence of bytes.
     */
    function method {:extern} sha3(bytes:seq<u8>) : u256 {
        0
    }

    /**
     * Compute the SHA256 hash of a sequence of bytes.
     */
    function method {:extern} sha256(bytes:seq<u8>) : seq<u8> {
        []
    }

    /**
     * Comput the RIPEMD160 digest.
     */
    function method {:extern} ripEmd160(bytes:seq<u8>) : seq<u8> {
        []
    }

    /**
     * Compute the Blake2(f) cryptographic hash.  See EIP152.
     */
    function method {:extern} blake2f(bytes:seq<u8>) : seq<u8> {
        []
    }

    /**
     * Compute arbitrary precision exponentiation under modulo.  Specifically,
     * we compue B^E % M.  All words are unsigned integers in big endian format.
     */
    function method {:extern} modExp(B: seq<u8>, E: seq<u8>, M: seq<u8>) : seq<u8> {
        []
    }
}
