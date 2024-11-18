import java.util.*;

class TestNode {
    TestNode f;
    TestNode g;
    TestNode() {}
}

public class Test {
    public static void main(String[] args) {
        TestNode a = new TestNode();
        a.f = new TestNode();
        a.f.f = new TestNode();
        a.f.f.f = new TestNode();
        a.f.f.f.f = new TestNode();
        a.f.f.f.f.f = new TestNode();
        TestNode b = foo(a);
        a = new TestNode();
    }

    static TestNode foo(TestNode x) {
        while(x != null) {
            x = x.f;
        }
        return x;
    }
}
