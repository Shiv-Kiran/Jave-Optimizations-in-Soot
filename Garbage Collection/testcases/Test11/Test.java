// Testcase 11:
// Handling more fields.

class TestNode {
	TestNode f;
	TestNode g;
}
public class Test {
	public static TestNode global;
	public static void main(String[] args) {
		foo();
	}
	public static TestNode foo(){
		TestNode x = new TestNode();
		x.f = new TestNode();
		x.f.g = new TestNode();
		TestNode y = new TestNode();
		TestNode z = new TestNode();
		y.f = z;
		bar(x.f, y);
		return y.f;
	}
	public static void bar(TestNode p1, TestNode p2){
		TestNode w = new TestNode();
		w.f = new TestNode();
		p2.f = w.f;
	}
}
