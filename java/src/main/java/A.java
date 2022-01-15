package org.rowland;

import java.util.Vector;
import java.util.TimeZone;

class A extends Object {
  String foo;
  String foo2;
  Integer bar;
  Boolean b;
  Vector v;

  A() {
    super();
    this.foo = "Rowland";
    this.foo2 = "Smit";
    this.bar = 5;
    this.b = true;
    this.v = new Vector();
  }

  A(String f) {
    this();
    this.foo = f;
  }

  Pair test(B foo, Pair bar) {
    return new Pair(foo, new A());
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
    return this.v.add(a);
  }

  Integer compare(String a) {
    return this.foo.compareTo(a);
  }

  Integer getCodePoint() {
    return this.foo.codePointAt(Math.min(Math.subtractExact(this.foo2.length(),1),Math.subtractExact(this.foo.length(),1)));
  }

  Integer calcFloorDiv(Integer a) {
    return java.lang.Math.floorDiv(this.bar,a);
  }

  Integer getStringFromInt(Integer a, Integer b) {
    return "SuperFoo".replaceAll(this.bar.equals(a) ? "Eq" : "Ne",this.bar.equals(a) ? "Eq" : "Ne").length();
    //return (this.bar.equals(a) ? "Eq" : "Ne");
  }

  Integer paramTester(String a, String b) {
    return this.getStringFromInt(a.equals("Ne") ? Integer.sum(4,2) : 2, b.equals("Ne") ? 3 : 1);
  }

  Object lubTest() {
    return (this.b ? new B() : new C());
  }

  String getDefaultTZ() {
    return TimeZone.getDefault().getDisplayName();
  }
}
