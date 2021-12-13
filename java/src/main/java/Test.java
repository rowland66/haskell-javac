class Pair extends Object {
  A fst;
  java.lang.Object snd;

  Pair(B fst, java.lang.Object snd) {
    this.fst=fst; this.snd=snd;
  }

  Pair setfst(java.lang.Object newfst, Pair test) {
    return new Pair((B) newfst, test);
  }

  A getSnd(A x, Pair r) {
    return ((Pair) this.fst.test((C) x,r)).fst;
  }

}

class B extends A {
  java.lang.Object bar;

  B() {
    super(new C());
    this.bar = new Pair(new B(), new A(new C()));
  }

  Pair test() {
    return new Pair(new B(), this.bar);
  }

}

class C extends B { C() { super(); } }
