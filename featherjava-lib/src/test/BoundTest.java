package test;

import java.io.Serializable;

public class BoundTest<F extends Number & Serializable> {

    final private F value;

    public BoundTest(F value) {
        this.value = value;
    }

    public F getValue() {
        return this.value;
    }
}
