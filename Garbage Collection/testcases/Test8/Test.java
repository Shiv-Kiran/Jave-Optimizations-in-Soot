// Testcase 5:
// Handling while loop.

class Test
{
	Test f1;
	public static void main(String[] args) {
		Test o1 = new Test();
		Test o2 = new Test();
		Test o3 = new Test();
		while (args.length > 0) {
			o3 = new Test();
		}
		Test o4 = o1.foo(o2);
		o3.f1 = o4;
		o4.f1 = new Test();
	}
	Test foo(Test p1) {
		Test o5 = new Test();
		Test o6 = new Test();
		Test o7 = bar();
		p1.f1 = o7;
		o5.f1 = o6;
 		return new Test();
	}
	static Test bar() {
		Test o8 = new Test();
		return o8;
	}

}
