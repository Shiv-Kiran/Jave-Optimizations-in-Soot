// Testcase 5:
// Handling conditionals.

class Test
{
	Test f;
	public static void main(String[] args) {
		Test ret = foo();
	}
	
	static Test foo() {
		Test x = new Test();
		Test y = x;
		for (int i = 0; i < 10; i++) {
			y.f = new Test();
			y = y.f;
		}
		return x;
	}
}
