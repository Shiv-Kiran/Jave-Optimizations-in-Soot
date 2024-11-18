// Testcase 4:
// Handling method call.

class Test
{
	Test f1;
	Test f2;
	public static void main(String[] args) {
		Test o1 = new Test();
		Test o2 = new Test();
		Test o3 = new Test();
		Test o4 = o1.foo(o2, o3);
		Test o5 = o1.bar(o4);
	}
	
	Test foo(Test p1, Test p2) {
		p1.f1 = new Test();
		p1.f1.f2 = new Test();
		p2.f1 = new Test();
		return p1;
	}
	
	Test bar (Test p3) {
		Test o5 = new Test();
		p3.f1 = new Test();	
		return o5;
	}
}
