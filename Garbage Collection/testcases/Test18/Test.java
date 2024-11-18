class TestNode {
	TestNode f;
	TestNode g;
	TestNode() {}
}

public class Test {
	public static void main(String[] args) {
		TestNode a = new TestNode(); //O1
		a.f = new TestNode(); //O2
		a.f.f = new TestNode(); // O3
		a.f.f.f = new TestNode(); //O4
		a.f.f.f.f = new TestNode(); //O5
		a.f.f.f.f.f = new TestNode(); //O6
		TestNode b = foo(a);
		a = new TestNode(); //O7
		// Lots of other code
	}

	static TestNode foo(TestNode x) {
		while(x != null) {
			x = x.f;
		}
		return x;
	}
}