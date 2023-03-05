package org.rowland;

import java.util.List;
import java.util.AbstractList;
import java.util.LinkedList;

class StrangeList extends AbstractList<String> {
  
  List<String> innerList;

  StrangeList() {
    super();
    this.innerList = new LinkedList<String>();
  }

  public String get(int i) {
    return this.innerList.get(i);
  }

  public int size() {
    return this.innerList.size();
  }
}

class WonkyList extends java.util.AbstractSequentialList<String> {

  java.util.List<String> l;

  WonkyList() {
    super();
    this.l = new java.util.LinkedList<String>();
  }

  public java.util.ListIterator<String> listIterator(int index) {
    return this.l.listIterator();
  }

  public int size() {
    return 0;
  }
}

