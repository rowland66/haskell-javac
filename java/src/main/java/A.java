package org.rowland;

class A extends Object {
  String foo;
  String foo2;
  Integer bar;
  Boolean b;

  A(C initFoo) {
    super();
    this.foo = "Rowland";
    this.foo2 = "Smit";
    this.bar = 5;
    this.b = true;
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
    return this.foo.concat(a); // This is another test comment.
  }

  Integer addInt(Integer a) {
    return featherjava.lang.IntegerMath.add(this.bar, featherjava.lang.IntegerMath.mul(a,2));
  }

  /**
    Calling method with parameters of different types, and boxing result.
   */
  Boolean test(Integer a) {
    return this.bar.equals(a);
  }

  Integer compare(String a) {
    return this.foo.compareTo(a);
  }

  Integer getCodePoint() {
    return this.foo.codePointAt(this.foo2.length());
  }

  Integer calcFloorDiv(Integer a) {
    return java.lang.Math.floorDiv(this.bar,a);
  }
}
