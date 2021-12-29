package org.rowland;

class A extends Object {
  String foo;
  Integer bar;
  Boolean b;

  A(C initFoo) {
    super();
    this.foo = "Rowland";
    this.bar = 5;
    this.b = true;
    //this.bar.bar = new C();
  }

  Pair test(B foo, Pair bar) {
    return new Pair(foo, new A(new C()));
  }

  Integer getInt() {
    return this.bar;
  }

  String getStr() {
    return this.foo.concat(" Smith").toUpperCase();
  }

  String addString(String a) {
    return this.foo.concat(a);
  }
}
