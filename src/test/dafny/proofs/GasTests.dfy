// Some tests related to gas.
include "../../../dafny/evm.dfy"
include "../../../dafny/evms/berlin.dfy"

module GasTests {
    import opened Int
    import EvmBerlin
    import Bytecode
    import opened Opcode
    import Gas

     /** The gas loaded in the EVM before executing a program. */
    const INITGAS := 0xFFFF;

    method test_01() {
        // Simple contract containing only one instruction.
        var vm := EvmBerlin.InitEmpty(gas := INITGAS, code := [GAS]);
        vm := EvmBerlin.Execute(vm);
        // Sanity check output!
        assert vm.Peek(0) == ((INITGAS - Gas.G_BASE) as u256);
    }
}
