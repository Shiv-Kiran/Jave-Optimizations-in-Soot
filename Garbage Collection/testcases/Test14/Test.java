// Testcase 5:
// Handling conditionals.

class Test
{
	public static void main(String[] args) {
		Test o1 = new Test();
		Test o2 = new Test();
		Test o3 = o1.foo(o2, true, false);
		Test o4 = o3;
	}
	
	Test foo(Test p1,boolean b,  boolean d ) {
		Test t1 = new Test();
		Test t2 = new Test();
		Test t3 = new Test();

		while (b) {
			if (b && d) {
				return t1;
			} else {
				return t2;
			}
		}
		return t3;
	}
}
