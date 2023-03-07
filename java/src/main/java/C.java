package org.rowland;

public class C extends A {
  AbstractTest absTest;

  public C() {
    super();
    this.absTest = new AbstractImpl();
  }

  public Integer getAbstractNumber() {
    return this.absTest.getMyNumber();
  }

  public  String getString() {
    return this.absTest.getString();
  }
}

