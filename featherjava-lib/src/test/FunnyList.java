package test;

import java.util.AbstractSequentialList;
import java.util.LinkedList;
import java.util.ListIterator;

public class FunnyList<F> extends AbstractSequentialList<String> {

    private LinkedList<String> l = new LinkedList<>();

    @Override
    public ListIterator<String> listIterator(int index) {
        return l.listIterator();
    }

    @Override
    public int size() {
        return 0;
    }

}
