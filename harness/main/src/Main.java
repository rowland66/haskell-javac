import org.rowland.*;

import java.util.List;

class Main {
    static Integer java = 5;
    public static void main(String[] args) {
        A a = new A("Bob");
        C c = new C();
        System.out.println(a.getStr());
        System.out.println(a.addString(" Long"));
        System.out.println(a.addInt(3));
        //Boolean b = a.test(4);
        //System.out.println(b);
        System.out.println(a.compare("Rowland"));
        System.out.println(a.getCodePoint());
        System.out.println(a.calcFloorDiv(4));
        System.out.println(a.getStringFromInt(4,2));
        System.out.println(a.paramTester("Ne", "Eq"));
        System.out.println(a.lubTest());
        System.out.println(a.getDefaultTZ());
        System.out.println(c.getAbstractNumber());
        System.out.println(c.getString());
        System.out.println(a.staticFieldTest(5));
        System.out.println(a.staticMethodTest());
        var testList = List.of(1,2,3);
        System.out.println(a.testPut(testList));
        System.out.println(a.testGet());
        List<Integer> l = a.e;

    }

    Integer a;

    public Main() {
        this.a = Integer.valueOf(5);
    }

    public Main(int i) {
        this();
        this.a = i;
    }
    public void test() {
        doit((Object) a);
    }

    public void doit(int a) {

    }

    public void doit(Object a) {

    }

    public boolean boxingTest(Integer b) {
        return new Boolean(true);
    }
}
