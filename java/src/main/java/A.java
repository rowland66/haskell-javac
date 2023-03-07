package org.rowland;

import java.util.Vector;
import java.util.List;
import java.util.LinkedList;
import java.util.TimeZone;
import test.BoundTest;
import featherjava.lang.IntegerMath;
import java.util.function.BinaryOperator;

public class A extends Object {
  String foo;
  String foo2;
  Integer bar;
  Boolean b;
  int c;

  public Vector<Number> v;
  public List<Integer> e;
  BoundTest<Integer> btest;

  public A() {
    super();
    this.foo = "Rowland";
    this.foo2 = "Smith";
    this.bar = 5;
    this.b = true;
    this.c = 0;
    this.v = new Vector<Number>();
    this.e = List.<Integer>of(1,2,3,4);
    this.btest = new BoundTest<Integer>(4);
  }

  public A(String f) {
    this();
    this.foo = f;
  }

  public Pair test(B foo, Pair bar) {
    return new Pair(foo, new A());
  }

  public Integer getInt() {
    return this.bar;
  }

  public String getStr() {
    return this.foo.concat(" Smith").toUpperCase();
  }

  public String addString(String a) {
    return this.foo.concat(a); // This is another test comment.
  }

  public Integer addInt(Integer a) {
    return featherjava.lang.IntegerMath.add(this.bar, featherjava.lang.IntegerMath.mul(a,2));
  }
  
  /**
    Calling method with parameters of different types, and boxing result.
  */

  public Boolean testPut(List<Integer> a) {
    return this.v.addAll(a);
  }

  public Number testGet() {
    return this.v.get(0);
  }

  public Integer compare(String a) {
    return this.foo.compareTo(a);
  }
  
  public Integer getCodePoint() {
    return this.foo.codePointAt(Math.min(Math.subtractExact(this.foo2.length(),1),Math.subtractExact(this.foo.length(),1)));
  }

  public Integer calcFloorDiv(Integer a) {
    return java.lang.Math.floorDiv(this.bar,a);
  }

  public Integer getStringFromInt(Integer a, Integer b) {
    return "SuperFoo".replaceAll(this.bar.equals(a) ? "Eq" : "Ne",this.bar.equals(a) ? "Eq" : "Ne").length();
    //return (this.bar.equals(a) ? "Eq" : "Ne");
  }

  public Integer paramTester(String a, String b) {
    return this.getStringFromInt(a.equals("Ne") ? Integer.sum(4,2) : 2, b.equals("Ne") ? 3 : 1);
  }

  public Object lubTest() {
    return (this.b ? new B() : new C());
  }

  public String getDefaultTZ() {
    return TimeZone.getDefault().getDisplayName();
  }

  public Integer abstractTest(Number a) {
    return a.intValue();
  }

  public Integer staticFieldTest(Integer a) {
    return Integer.BYTES;
  }

  public Integer staticMethodTest() {
    return this.bar.bitCount(this.bar);
  }
  
  public List<Integer> createList(Integer a, Integer b, Integer c) {
    return List.<Integer>of(a,b,c);
  }

  public Integer getListInt() {
    return this.createList(1,2,3).get(1);
  }
  
  public Integer getStringFromIntList() {
    return this.getStringFromInt(this.createList(1,2,3).get(0), 12);
  }

  public Integer getBoundTestValue() {
    return this.btest.getValue();
  }

  public Integer listSum() {
    return this.e.stream().<Integer>reduce(0, new SumMaker());
  }
}

class SumMaker implements BinaryOperator<Integer> {
  
  public SumMaker() {
    super();
  }

  public Integer apply(Integer a, Integer b) {
    return IntegerMath.add(a, b);
  }
}

/**
class StringReaderTest extends Object {

  StringReaderTest() {
    super();
  }

  Integer readData(Readable readable) {
    return readable.read(java.nio.CharBuffer.allocate(128).append("Good evening sir."));
  }

  java.nio.CharBuffer getBuffer() {
    return java.nio.CharBuffer.allocate(128).append("Good evening sir.");
  }
*/ 

