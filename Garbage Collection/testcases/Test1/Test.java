// Testcase 1:
// Handling 3 objects in single method

class Test
{
	Test f1;
	public static void main(String[] args) {
		Test o1 = new Test();
		Test o2 = new Test();
		Test o3 = new Test();
		o1.f1 = o2;
		o2.f1 = o3;
	}
}
