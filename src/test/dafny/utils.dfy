
module Utils {
  // A simple method which ensures a given predicate is verified,
  // and also checked at runtime.
  method AssertAndExpect(p: ()->bool)
  requires p() {
    expect p();
  }
}