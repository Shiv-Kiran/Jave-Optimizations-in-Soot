// Testcase 6:
// Handling Inheritance

class Test
{
	Test f1;
	Test f2;
	public static void main(String[] args) {
		Test o1 = new Test();
		foo(o1);
	}
	static void foo(Test p1) {
		p1.f1 = new Test();
		p1.f1.f2 = new Test();
		p1.f1.f1 = new Test();
		p1.f1.f1.f1 = new Test();
		p1.f1.f1.f1.f1 = new Test();
		p1.f1.f1.f1.f1.f1 = new Test();
		p1.bar();
	}
	void bar() {
		this.f1 = new Test();
	}
}
