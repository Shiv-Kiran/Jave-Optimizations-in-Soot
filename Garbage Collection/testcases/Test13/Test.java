// Testcase 5:
// Handling conditionals.

class Test
{
	Test f1;
	public static void main(String[] args) {
		Test o1 = new Test();
		Test o2 = new Test();
		o1.foo(o2);
	}
	
	void foo(Test p1) {
		Test o3 = new Test();
		o3.bar(p1);
	}

	void bar(Test p2) {
		Test o4 = new Test();
		o4.foobar(p2);
	}

	void foobar(Test p3) {
		Test o5 = new Test();
		o5.fb(p3);
	}

	void fb(Test p4) {
		Test o6 = new Test();
		o6.f1 = p4;
	}
}