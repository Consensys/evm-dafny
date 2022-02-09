


include "NonNativeTypes.dfy"
import opened NonNativeTypes

/** The type fo the EVM stack. 
 * 
 *  @note   The stack can contain at most 1024 items which is not captured
 *          by this type definition. 
 */
type EVMStack = seq<uint256>

/** 
 *  Provide an initialiased EVM.
 */
class EVM {

    /** The stack of the VM. */
    var stack: EVMStack
    var gas: uint256

    /** Init the VM. */
    constructor (g: uint256) 
        ensures stack == []
    {
        stack := []; 
        gas := g;
    }

    /** 
     *  PUSH1 opcode.
     */
    method push1(v: uint256) 
        ensures |stack| == |old(stack)| + 1
        ensures stack == [v] + old(stack)

        modifies `stack, `gas
    {
        stack := [v] + stack;
    }

    /**
     *  POP opcode.
     */
    method pop() 
        requires |stack| > 0 

        ensures |stack| == |old(stack)| - 1
        ensures stack == old(stack)[1..]

        modifies `stack 
    {
        stack := stack[1..]; 
    }

    /**
     *  SWAP1 opcode.
     */
    method swap1()  
        requires |stack| >= 2

        ensures |stack| == |old(stack)|
        ensures stack[0] == old(stack)[1]
        ensures stack[1] == old(stack)[0]
        ensures stack[2..] == old(stack)[2..]

        modifies `stack 
    {
        stack := [stack[1]] + [stack[0]] + stack[2..];
    }


    /**
     *  ADD opcode.
     */
    method add()  
        requires |stack| >= 2
        requires stack[0] as nat + stack[1] as nat <= MAX_UINT256

        ensures |stack| == |old(stack)| - 1
        ensures stack[0] == old(stack)[0] + old(stack)[1]
        ensures stack[1..] == old(stack)[2..]

        modifies `stack 
    {
        stack := [stack[0] + stack[1]] + stack[2..];
    }

    /**
     *  SUB opcode. compute stack[1] - stack[0], which is not the semantics
     *  of SUB that is stack[0] - stack[1]
     */
    method subR()  
        requires |stack| >= 2
        requires stack[1] as nat - stack[0] as nat >= 0

        ensures |stack| == |old(stack)| - 1
        ensures stack[0] == old(stack)[1] - old(stack)[0]
        ensures stack[1..] == old(stack)[2..]

        modifies `stack 
    {
        stack := [stack[1] - stack[0]] + stack[2..];
    }

    /**
     *  SUB opcode. compute stack[0] - stack[1], which is the
     *  real semantics of sub 
     */
    method sub()  
        requires |stack| >= 2
        requires stack[0] as nat - stack[1] as nat >= 0

        ensures |stack| == |old(stack)| - 1
        ensures stack[0] == old(stack)[0] - old(stack)[1]
        ensures stack[1..] == old(stack)[2..]

        modifies `stack 
    {
        stack := [stack[0] - stack[1]] + stack[2..];
    }

    /**
     *  DUP2 opcode. Duplicate the second element of the stack.
     */
    method dup2()  
        requires |stack| >= 2

        ensures |stack| == |old(stack)| + 1
        ensures stack == [old(stack)[1]] + old(stack)

        modifies `stack 
    {
        stack := [stack[1]] + stack;
    }

    /**
     *  GT opcode. Compute stack[0] > stack[1] and store result. 
     */
    method gt()  
        requires |stack| >= 2

        ensures |stack| == |old(stack)| - 1
        ensures stack == [if (old(stack)[0] > old(stack)[1]) then 1 else 0] + old(stack)[2..]

        modifies `stack 
    {
        if (stack[0] > stack[1]) {
            stack := [1] + stack[2..];
        } else {
            stack := [0] + stack[2..];
        }
    }

}

method main1() 
{
    var e := new EVM(0);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    ghost var g := e.stack;

    e.push1(a);
    e.push1(b);
    e.add();

    assert e.stack[0] == a + b;

    e.pop();
    assert e.stack == g;
}

method main2(c: uint256) 
{
    var e := new EVM(0);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;
    var count: uint256 := c;

    ghost var g := e.stack;

    while count > 0 
        invariant  e.stack == g
    {
        e.push1(a);
        e.push1(b);
        e.add();
        e.pop();
        count := count - 1 ;
    }
    
    assert e.stack == g;
}

/**
 *  Without a swap1, use an alternative semantics of SUB.
 */
method main3(c: uint256) 
{
    var e := new EVM(0);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    e.push1(c);
    ghost var g := e.stack;
    ghost var count := c;

    assert count == e.stack[0];

    while e.stack[0] > 0 
        invariant  |e.stack| > 0  
        invariant count == e.stack[0]
        invariant e.stack == [count]
    {

        e.push1(a);
        e.push1(b);
        e.add();
        e.pop();

        //  count := count - 1 ;
        e.push1(0x1);
        e.subR();
        count := count - 1;
        
    }
    assert count == 0;
    assert e.stack == [0];
}

/**
 * Use real semamtics of SUB and a swap1.
 */
method main4(c: uint256)  
{
    var e := new EVM(0);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    e.push1(c);
    ghost var g := e.stack;
    ghost var count := c;

    assert count == e.stack[0];

    while e.stack[0] > 0 
        invariant  |e.stack| > 0  
        invariant count == e.stack[0]
    {

        e.push1(a);
        e.push1(b);
        e.add();
        e.pop();

        //  count := count - 1 ;
        e.push1(0x1);
        e.swap1();
        e.sub();

        count := count - 1;
        
    }
}

/**
 * Use real semantics of SUB and a swap1, and test top of stack with LT/GT
 *  instead of e.stack[0] > 0 
 */
method main5(c: uint256)  
{
    var e := new EVM(0);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    e.push1(c);
    ghost var g := e.stack;
    ghost var count := c;

    //  stack = [count]
    assert count == e.stack[0];

    //  compute count > 0 

    //  top of the stack has the result of count > 0
    //  push 0, then duplicate second element on top
    e.push1(0x0);
    e.dup2();
    //  stack = [count, 0, count]
    //  compute stack[0] > stack[1]
    e.gt();
    //  stack = [count > 0, count]

    assert(count == e.stack[1]); 

    while e.stack[0] > 0 
        invariant  |e.stack| > 1  
        invariant count == e.stack[1] >= 0
        invariant e.stack[0] > 0 <==> count > 0
        invariant |e.stack| == 2

        decreases count
    {
        //  top of the stack is the last result of stack[0] > stack[1]
        e.pop();
        //  stack = [count] 
        //  a + b and discard result
        e.push1(a);
        e.push1(b);
        e.add();
        e.pop();

        assert count == e.stack[0] ;
        assert count > 0;
        //  count := count - 1 ;
        e.push1(0x1);
        e.swap1();
        //  stack = [count, 1]
        e.sub();
        //  stack = [count - 1]

        //  prepare comparison count > 0. count is at the top
        e.push1(0x0);
        e.dup2();
        //  stack = [count - 1, 0, count - 1]
        //  compute stack[0] > stack[1]
        e.gt();        
        //  stack = [count - 1 > 0, count - 1]
        count := count - 1;
        
    }
    assert count == e.stack[1];
    e.pop();
    assert e.stack[0] == count;
    assert count == 0;
    assert |e.stack| == 1;
    assert e.stack == [0];

}

/**
 * Use gas cost.
 */
method main6(c: uint256, g: uint256)  
{
    var e := new EVM(g);
    var a: uint256 := 0x01;
    var b : uint256 := 0x02;

    e.push1(c);
    ghost var g := e.stack;
    ghost var count := c;

    //  stack = [count]
    assert count == e.stack[0];

    //  compute count > 0 

    //  top of the stack has the result of count > 0
    //  push 0, then duplicate second element on top
    e.push1(0x0);
    e.dup2();
    //  stack = [count, 0, count]
    //  compute stack[0] > stack[1]
    e.gt();
    //  stack = [count > 0, count]

    assert(count == e.stack[1]); 

    while e.stack[0] > 0 
        invariant  |e.stack| > 1  
        invariant count == e.stack[1] >= 0
        invariant e.stack[0] > 0 <==> count > 0
        invariant |e.stack| == 2

        decreases count
    {
        //  top of the stack is the last result of stack[0] > stack[1]
        e.pop();
        //  stack = [count] 
        //  a + b and discard result
        e.push1(a);
        e.push1(b);
        e.add();
        e.pop();

        assert count == e.stack[0] ;
        assert count > 0;
        //  count := count - 1 ;
        e.push1(0x1);
        e.swap1();
        //  stack = [count, 1]
        e.sub();
        //  stack = [count - 1]

        //  prepare comparison count > 0. count is at the top
        e.push1(0x0);
        e.dup2();
        //  stack = [count - 1, 0, count - 1]
        //  compute stack[0] > stack[1]
        e.gt();        
        //  stack = [count - 1 > 0, count - 1]
        count := count - 1;
        
    }
    assert count == e.stack[1];
    e.pop();
    assert e.stack[0] == count;
    assert count == 0;
    assert |e.stack| == 1;
    assert e.stack == [0];

}

