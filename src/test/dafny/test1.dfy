include "../../dafny/evm.dfy"

import opened Int
import opened EVM

// Arbitrary limit for now
const GASLIMIT : nat := 100;

// Check most simple program possible
// method {:test} test1()
method {:test} test1()
{
  var x := 3;
  // Initialise EVM
  var tx := Context.Create(0xabcd,[]);
  var vm := EVM.Create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
  // PUSH1 x
  vm := EVM.Execute(vm);
  // PUSH1 0x2
  vm := EVM.Execute(vm);
  // MSTORE
  vm := EVM.Execute(vm);
  // PUSH
  vm := EVM.Execute(vm);
  // PUSH
  vm := EVM.Execute(vm);
  // RETURN
  vm := EVM.Execute(vm);
  //
  expect vm.data == [x+1], ("failed. vm.data=", vm.data); //, "failed";
  // print vm.data, "\n";
}

// // ===========================================================================
// // Straightline Tests
// // ===========================================================================

// // Write parameter into return data
// method test_basic_01(x: u8)
// requires x > 1
// {
//   var tx := Context.Create(0xabcd,[]);
//   var vm := EVM.Create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
//   //
//   vm := EVM.Push1(vm,x);
//   vm := EVM.Push1(vm,0);
//   vm := EVM.MStore(vm);
//   vm := EVM.Push1(vm,0x1);
//   vm := EVM.Push1(vm,0x1F);
//   vm := EVM.Return(vm);
//   //
//   assert vm.data  == [x];
// }

// // Add two values and return
// method test_basic_02(x: u8, y: u8) returns (z:u16)
// ensures z == (x as u16) + (y as u16)
// {
//   var tx := Context.Create(0xabcd,[]);
//   var vm := EVM.Create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, y, ADD, PUSH1, 0x0, MSTORE, PUSH1, 0x2, PUSH1, 0x1E, RETURN]);
//   //
//   vm := EVM.Push1(vm,x);
//   vm := EVM.Push1(vm,y);
//   vm := EVM.Add(vm);
//   assert vm.Peek(0) == (x as u256) + (y as u256);
//   vm := EVM.Push1(vm,0);
//   vm := EVM.MStore(vm);
//   vm := EVM.Push1(vm,0x2);
//   vm := EVM.Push1(vm,0x1E);
//   vm := EVM.Return(vm);
//   // //
//   return Bytes.ReadUint16(vm.data,0);
// }

// method test_basic_03(x: u8, y: u8) returns (z:u8)
// requires x >= y
// ensures z <= x
// {
//   var tx := Context.Create(0xabcd,[]);
//   var vm := EVM.Create(tx,map[],GASLIMIT,[PUSH1, y, PUSH1, x, SUB, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
//   //
//   vm := EVM.Push1(vm,y);
//   vm := EVM.Push1(vm,x);
//   vm := EVM.Sub(vm); // x - y
//   vm := EVM.Push1(vm,0);
//   vm := EVM.MStore(vm);
//   vm := EVM.Push1(vm,0x1);
//   vm := EVM.Push1(vm,0x1F);
//   vm := EVM.Return(vm);
//   //
//   return Bytes.ReadUint8(vm.data,0); 
// }

// // ===========================================================================
// // Branching Tests
// // ===========================================================================

// // This is an underflow test.  Either the contract reverts, or there was no underflow.
// method test_branch_01(x: u8, y: u8) returns (z:u8, revert:bool)
//   // Check revert only when overflow would have occurred.
//   ensures revert <==> y > x
//   // If didn't revert, then result is less.
//   ensures !revert <==> (z <= x)
// {
//   var tx := Context.Create(0xabcd,[]);
//   var vm := EVM.Create(tx,map[],GASLIMIT,[PUSH1, x, PUSH1, y, GT, ISZERO, PUSH1, 0x0A, JUMPI, REVERT, JUMPDEST, PUSH1, x, PUSH1, y, SUB, PUSH1, 0x0, MSTORE, PUSH1, 0x1, PUSH1, 0x1F, RETURN]);
//   //
//   vm := EVM.Push1(vm,x);   // 0x00
//   vm := EVM.Push1(vm,y);   // 0x02
//   vm := EVM.Gt(vm);        // 0x04
//   vm := EVM.IsZero(vm);    // 0x05
//   vm := EVM.Push1(vm,0xA); // 0x06
//   vm := EVM.JumpI(vm);     // 0x08
//   //
//   assert vm.PC() == 0x09 <==> y > x;
//   if vm.PC() == 0x09 {
//     vm := EVM.Revert(vm);  // 0x09
//     return y,true;
//   } else {
//     // Happy path
//     vm := EVM.JumpDest(vm); // 0xA
//     assert x >= y;
//     vm := EVM.Push1(vm,y);
//     vm := EVM.Push1(vm,x);
//     vm := EVM.Sub(vm); // x - y
//     vm := EVM.Push1(vm,0);
//     vm := EVM.MStore(vm);
//     vm := EVM.Push1(vm,0x1);
//     vm := EVM.Push1(vm,0x1F);
//     vm := EVM.Return (vm);
//     Foo(x, y);
//     //
//     return Bytes.ReadUint8(vm.data,0), false;
//   }
// }

// lemma Foo(x:u8, y:u8) 
//   ensures y <= x ==> x - y <= x
// {

// }

// // ===========================================================================
// // Looping Tests
// // ===========================================================================

method main5(c: u8)  
{
    var end : u8 := 17;
    var a: u8 := 0x01;
    var b : u8 := 0x02;

    //  EVM
    // Initialise EVM 
    var tx := Context.Create(0xabcd,[]);
    var vm := EVM.Create(tx, map[], GASLIMIT,
        [
            PUSH1, c,       //  0
            JUMPDEST,       //  2
            DUP1,           //  3
            ISZERO,         //  4
            DUP1,           //  5
            PUSH1, end,     //  6
            JUMPI,          //  8
            POP,            //  9
            PUSH1, 1,       // 10
            SWAP1,          // 12
            SUB,            // 13
            PUSH1, 2,       // 14 
            JUMP,           // 16
            JUMPDEST,       // 17
            STOP            // 18
        ]
    );

    //  snapshot of code
    ghost var code_ := vm.evm.code;

    ghost var count :u256 := c as u256; 

    //  push input on the stack
    //  check that pc is zero and code under pc is push1
    assert vm.PC() == 0;
    assert vm.evm.code.contents[vm.PC()] == PUSH1;
    assert vm.PC() == 0;
    assert vm.evm.code.contents[vm.PC() + 1] == c;
    assert vm.GetStack() == Stack.Make([]); 

    vm := EVM.Push1(vm, c);  
    // assert count == e.stack[0];
    assert vm.GetStack() == Stack.Make([count]);
    assert vm.Peek(0) == count;

    vm := EVM.JumpDest(vm);  
    // assert count == e.stack[0];
    assert vm.GetStack() == Stack.Make([count]);
    assert vm.Peek(0) == count;

    // Compute result of test c > 0
    assert vm.evm.code.contents[vm.PC()] == DUP1;
    vm := EVM.Dup(vm, 1);  
    assert vm.GetStack() == Stack.Make([count, count]);

    assert vm.evm.code.contents[vm.PC()] == ISZERO;
    vm := EVM.IsZero(vm); 
    // e.iszero(); [count == 0, count]
    assert vm.GetStack() == Stack.Make([if count == 0 then 1 else 0, count]);

    assert vm.evm.code.contents[vm.PC()] == DUP1;
    vm := EVM.Dup(vm, 1); 
    // e.dup1();  [count == 0, count == 0, count]
    assert vm.GetStack() == Stack.Make([if count == 0 then 1 else 0, if count == 0 then 1 else 0, count]);

    //  if count == 0 jump to end 
    assert vm.evm.code.contents[vm.PC()] == PUSH1;
    assert vm.evm.code.contents[vm.PC() + 1] == end;
    vm := EVM.Push1(vm, end); 
    // e.push(end);  // [end, count == 0, count == 0, count]
    assert vm.GetStack() == Stack.Make([end as u256, if count == 0 then 1 else 0, if count == 0 then 1 else 0, count]); 

    assert vm.evm.code.contents[vm.PC()] == JUMPI;
    vm := EVM.JumpI(vm);
    //  e.jumpi();  // [count == 0, count]
    assert vm.GetStack() == Stack.Make([if count == 0 then 1 else 0, count]); 
    // assert count == e.stack[1];

    // assert vm.evm.code.contents[8] == POP; 
    // assert vm.evm.code.contents[9] == PUSH1; 

    //  this test/while loop is in main5 only, not in the bytecode.
    //  it corresponds to P1 choosing its strategy to match the bytecode.
    while vm.evm.stack.contents[0] == 0 // checkPeek(vm, 0, 0) // e.stack[0] == 0   
        invariant !vm.IsFailure()
        invariant vm.evm.code.contents == code_.contents   //  code is not changed
        invariant |vm.evm.stack.contents| > 1              //  stack not empty
        invariant vm.Capacity() >= 2                    //  capacity >= 2 on entry
        invariant vm.Peek(1) == count
        invariant count == 0 <==> vm.Peek(0) > 0 
        invariant vm.Peek(0) == 0 <==> vm.PC() == 9
        invariant vm.Peek(0) > 0 <==> vm.PC() == 17


        decreases count
    {
        assert vm.Slice(0,2) == Stack.Make([0, count]);    

        assert vm.evm.code.contents[vm.PC()] == POP; 
        //  e.pop();  [count]
        vm := EVM.Pop(vm); 
        assert vm.evm.stack.contents[..1] == [count];     

        // e.push(0x1); [1, count]
        assert vm.evm.code.contents[vm.PC()] == PUSH1; 
        assert vm.evm.code.contents[vm.PC() + 1] == 0x1; 
        vm := EVM.Push1(vm, 1);
        assert vm.Slice(0,2) == Stack.Make([1, count]);    

        // e.swap1(); [count, 1]
        assert vm.evm.code.contents[vm.PC()] == SWAP1; 
        vm := EVM.Swap(vm, 1);
        assert vm.Slice(0,2) == Stack.Make([count,1 ]);  

        //  e.sub();  [count - 1] 
        assert vm.evm.code.contents[vm.PC()] == SUB; 
        vm := EVM.Sub(vm);
        assert vm.Slice(0, 1) == Stack.Make([count - 1]); 

        // jump to 2   
        // e.push(2); [2, count - 1]
        // e.jump();       // [count - 1]
        assert vm.evm.code.contents[vm.PC()] == PUSH1; 
        assert vm.evm.code.contents[vm.PC() + 1] == 0x2; 
        // assert vm.PC() as nat + 2 < |vm.Unwrap().code.contents|;
        vm := EVM.Push1(vm, 2);
        // assert vm.evm.stack.contents[0] == 2; 
        // assert vm.evm.stack.contents[1] == count - 1 ; 
        // assert vm.OK?;
        assert vm.Slice(0, 2) == Stack.Make([2, count - 1]);  

        // assert vm.PC() == 15;
        assert vm.evm.code.contents[vm.PC()] == JUMP; 
        vm := Jump(vm);
        assert vm.evm.stack.contents[..1] == [count - 1]; 

        assert vm.evm.code.contents[vm.PC()] == JUMPDEST; 
        vm := JumpDest(vm);  
        assert vm.Slice(0,1) == Stack.Make([count - 1]); 

        // Compute result of test c > 0, same as before the loop
        count := count - 1;

        assert vm.evm.code.contents[vm.PC()] == DUP1;
        vm := EVM.Dup(vm, 1);  
        // e.dup1();  [count, count]
        assert vm.evm.stack.contents[..2] == [count, count];

        assert vm.evm.code.contents[vm.PC()] == ISZERO;
        vm := EVM.IsZero(vm); 
        // e.iszero(); [count == 0, count]
        assert vm.evm.stack.contents[..2] == [if count == 0 then 1 else 0, count];

        assert vm.evm.code.contents[vm.PC()] == DUP1;
        assert vm.PC() as nat  < |vm.Unwrap().code.contents|; 

        vm := EVM.Dup(vm, 1); 
        assert vm.OK?;
        // e.dup1();  [count == 0, count == 0, count]
        assert vm.Slice(0,3) == Stack.Make([if count == 0 then 1 else 0, if count == 0 then 1 else 0, count]);   
 
        //  if count == 0 jump to end  
        assert vm.evm.code.contents[vm.PC()] == PUSH1;
        assert vm.evm.code.contents[vm.PC() + 1] == end;
        vm := EVM.Push1(vm, end); 
        // e.push(end);  // [end, count == 0, count == 0, count]
        assert vm.Slice(0,4) == Stack.Make([end as u256, if count == 0 then 1 else 0, if count == 0 then 1 else 0, count]);  

        assert vm.evm.code.contents[vm.PC()] == JUMPI; 
        vm := EVM.JumpI(vm);
        //  e.jumpi();  // [count == 0, count]
        assert vm.Slice(0,2) == Stack.Make([if count == 0 then 1 else 0, count]); 
    }
    // end of program
    assert vm.evm.code.contents[vm.PC()] == JUMPDEST;
    vm := JumpDest(vm);

    // e.stop();
    assert vm.evm.code.contents[vm.PC()] == STOP;
    vm := Stop(vm);
    assert vm.RETURNS?;
}
