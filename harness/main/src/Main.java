import org.rowland.*;
import java.lang.String;

class Main {
    public static void main(String[] args) {
        Object o = new Object();
        A t = new A(new C());
        t.foo = "Hello";
        t.bar = new C();
        System.out.println(t.foo + t.toString());
    }
}
