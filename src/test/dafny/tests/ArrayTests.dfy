include "../../../dafny/util/arrays.dfy"
include "../utils.dfy"

module ArrayTests{
    import opened Arrays
    import opened Utils

    method {:test} CopyTests() {
        // n=0
        AssertAndExpect(Copy([],[1,2,3],0) == [1,2,3]);
        // n=1
        AssertAndExpect(Copy([4],[1,2,3],0) == [4,2,3]);
        AssertAndExpect(Copy([4],[1,2,3],1) == [1,4,3]);
        AssertAndExpect(Copy([4],[1,2,4],2) == [1,2,4]);
        // n=2
        AssertAndExpect(Copy([4,5],[1,2,3],0) == [4,5,3]);
        AssertAndExpect(Copy([4,5],[1,2,3],1) == [1,4,5]);
    }
}
