package org.rowland;

class Pair extends java.lang.Object {
  A fst;
  java.lang.Object snd;

  Pair(A fst, java.lang.Object snd) {
    this.fst=fst; this.snd=snd;
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

  String toString() {
    return "I'm a B";
  }
}

class C extends A {
  C() {
    super();
  }
}
