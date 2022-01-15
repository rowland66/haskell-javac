    import org.rowland.*;

class Main {
    static Integer java = new Integer(5);
    public static void main(String[] args) {
        A a = new A("Bob");
        System.out.println(a.getStr());
        System.out.println(a.addString(" Long"));
        System.out.println(a.addInt(3));
        Boolean b = a.test(4);
        System.out.println(b);
        System.out.println(a.compare("Rowland"));
        System.out.println(a.getCodePoint());
        System.out.println(a.calcFloorDiv(4));
        System.out.println(a.getStringFromInt(4,2));
        System.out.println(a.paramTester("Ne", "Eq"));
        System.out.println(a.lubTest());
        System.out.println(a.getDefaultTZ());
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
