class TestNode {
	TestNode f;
	TestNode g;
	TestNode() {}
}

public class Test {
	public static TestNode global;
	public static void main(String[] args) {
		foo();
	}
	public static TestNode foo(){
		TestNode x = new TestNode();
		TestNode y = new TestNode();
		Child a = new Child();
		Child b = new SecondChild();
		x.f = new TestNode();
		bar(x, y);
		a.baz(x, y);
		b.baz(x, y);
		return x;
	}
	public static void bar(TestNode p1, TestNode p2){
		TestNode v = new TestNode();
		p1.f = v;
	}
}

class Child {
	public void baz(TestNode n, TestNode m) {
		m.f = new TestNode();
	}
}

class SecondChild extends Child {
	public void baz(TestNode n, TestNode m) {
		Child a = new Child();
		n.f = new TestNode();
		System.out.println(a);
	}
}