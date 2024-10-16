
include "arrays.dfy"
include "int.dfy"

module External {
    import opened Arrays
    import opened Int
    /**
     * Compute the SHA3 (a.k.a KECCAK256) hash of a sequence of bytes.
     */
    // function {:extern} sha3(bytes:Array<u8>) : u256

    // /**
    //  * Comput the RIPEMD160 digest.
    //  */
    // function {:extern} ripEmd160(bytes:Array<u8>) : Array<u8>

    // /**
    //  * Compute the Blake2(f) cryptographic hash.  See EIP152.
    //  */
    // function {:extern} blake2f(bytes:Array<u8>) : Array<u8>

    // /**
    //  * Compute arbitrary precision exponentiation under modulo.  Specifically,
    //  * we compue B^E % M.  All words are unsigned integers in big endian format.
    //  */
    // function {:extern} modExp(B: Array<u8>, E: Array<u8>, M: Array<u8>) : Array<u8>
}
