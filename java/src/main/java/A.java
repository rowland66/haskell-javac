class A extends Object {
  java.lang.Object foo;
  B bar;

  A(C initFoo) {
    super();
    this.foo = initFoo;
    this.bar = new B();
    this.bar.bar = new C();
  }

  Pair test(C foo, Pair bar) {
    return new Pair(new B(), new A(new C()));
  }
}
