import org.rowland.*;

class Main {
    public static void main(String[] args) {
        A t = new A(new C());
        t.foo = "Hello";
        t.bar = new C();
        System.out.println(t.foo + t.toString());
    }
}
