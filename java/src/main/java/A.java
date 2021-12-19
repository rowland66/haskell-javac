package org.rowland;

class A extends java.lang.Object {
  java.lang.Object foo;
  C bar;

  A(C initFoo) {
    super();
    this.foo = initFoo;
    this.bar = new C();
    //this.bar.bar = new C();
  }

  Pair test(B foo, Pair bar) {
    return new Pair(foo, new A(new C()));
  }
}
