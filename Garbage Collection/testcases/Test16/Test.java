public class Test {
	Test f1;
	public static void main(String[] args) {
		Test o1 = new Test();
		Test o2 = new Test();
		o1.f1 = o2;
		Test o3 = new Test();
		Test o4 = o1.foo(o2);
		Test o5 = new Test();
		o5.f1 =  o4;
	}
	Test foo(Test p1) {
		Test o6 = new Test();
		p1.f1 = new Test();
		return o6;
	}
}