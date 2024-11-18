// Testcase 2:
// Handling conditionals

class Test
{
	Test f1;
	public static void main(String[] args) {
		Test o1;
		if(args.length > 0) {
			o1 = new Test();
		} else {
			o1 = new Test();
		}
		o1.f1 = new Test();
		Test o2 = o1.f1;
		o1 = new Test();
	}
}
