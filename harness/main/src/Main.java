import org.junit.Assert;
import org.junit.Test;
import org.rowland.*;

import java.util.AbstractList;
import java.util.List;
import java.util.Optional;

public class Main {

    Integer a;

    public Main() {
        this.a = Integer.valueOf(5);
    }

    @Test
    public void basicTest() {
        A a = new A("Bob");
        C c = new C();
        Assert.assertEquals("BOB SMITH", a.getStr());
        Assert.assertEquals("Bob Long", a.addString(" Long"));
        Assert.assertEquals(Integer.valueOf(11), a.addInt(3));
        Assert.assertTrue("Compare", a.compare("Bob") == 0);
        Assert.assertEquals(Integer.valueOf(98), a.getCodePoint());
        Assert.assertEquals(Integer.valueOf(1), a.calcFloorDiv(4));
    }

    @Test
    public void genericsTest() {
        A a = new A("Bob");
        var testList = List.<Integer>of(1,2,3);
        var testList2 = List.<Integer>of(4,5,6);

        Assert.assertTrue("testPut()",a.testPut(testList));
        Assert.assertEquals(1, a.testGet());
        List<Integer> l = a.e;
        Assert.assertTrue("containsAll", a.v.containsAll(testList));
        Assert.assertEquals(testList, a.createList(testList.get(0),testList.get(1),testList.get(2)));
        Assert.assertEquals(Integer.valueOf(2), a.getListInt());
        Assert.assertEquals(Integer.valueOf(4), a.getBoundTestValue());
        Assert.assertEquals(Integer.valueOf(10), a.listSum());
    }
    static Integer java = 5;
    public static void foo(String[] args) {
        A a = new A("Bob");
        C c = new C();
        System.out.println(a.getStringFromInt(4,2));
        System.out.println(a.paramTester("Ne", "Eq"));
        System.out.println(a.lubTest());
        System.out.println(a.getDefaultTZ());
        System.out.println(c.getAbstractNumber());
        System.out.println(c.getString());
        System.out.println(a.staticFieldTest(5));
        System.out.println(a.staticMethodTest());
    }
}
