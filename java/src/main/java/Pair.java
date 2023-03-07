package org.rowland;

class Pair extends java.lang.Object {
  A fst;
  java.lang.Object snd;

  Pair(A fst, java.lang.Object snd) {
    super(); this.fst=fst; this.snd=snd;
  }

  Pair setfst(java.lang.Object newfst, Pair test) {
    return new Pair((B) newfst, test);
  }

  A getSnd(A x, Pair r) {
    return ((Pair) this.fst.test((B) x,r)).fst;
  }

}

class B extends A {

  B() {
    super();
  }

}

abstract class AbstractTest {

  AbstractTest() {
    super();
  }

  abstract Integer getNumber();

  String getString() {
    return this.toString();
  }

  Integer getMyNumber() {
    return this.getNumber();
  }
}

class AbstractImpl extends AbstractTest {

  AbstractImpl() {
    super();
  }

  Integer getNumber() {
    return 5;
  }
}