package test;

import java.util.LinkedList;

public class FunnyList<F> extends LinkedList<String> {

    private static LinkedList<String> staticVar;

    @Override
    public String getFirst() {
        return super.getFirst();
    }
}
