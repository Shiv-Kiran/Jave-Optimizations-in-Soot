// Testcase 3:
// Handling Loops

class Test {
	Test f1;
	Test f2;

	public static void main(String[] args) {
		Test o1 = new Test();
		Test o2;
		while (args.length > 0) {
			o2 = new Test();
			o2.f1 = new Test();
			if (args.length > 1) {
				o2.f1.f1 = new Test();
			} else {
				o2.f1.f2 = new Test();
			}
			o2.f1.f1 = o1;
		}
		o2 = new Test();
		o2.f1 = o1;
	}
}