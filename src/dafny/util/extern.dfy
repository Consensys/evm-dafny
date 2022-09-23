
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
}
