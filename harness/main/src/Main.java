import org.rowland.*;

class Main {

    public static void main(String[] args) {
        A a = new A(new C());
        System.out.println(a.getStr());
        System.out.println(a.addString(" Long"));
    }
}
