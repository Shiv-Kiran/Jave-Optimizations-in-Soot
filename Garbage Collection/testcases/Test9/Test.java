// Testcase 9:
// Handling Maps

import java.util.HashMap;

class Test
{
	Test f1;
	public static void main(String[] args) {
		Test o1 = new Test();
		Test o2 = new Test();
		for(int i = 1; i < 10; i++) {
			o1.foo(o2);
		}
		o1.foo(o2);
	}
	
	void foo(Test p1) {
		Test o3 = new Test();
		Test o4 = new Test();
		o3.f1 = o4;
		o4.f1 = new Test();
	}
}
