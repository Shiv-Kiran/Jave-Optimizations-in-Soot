// Testcase 7:
// Handling Inheritance with more objects.

class Test
{
	Test f1;
	Test f2;
	public static void main(String[] args) {
		Test o1 = new Test();
		Test o2 = new Test();
		Test o3 = new Test();
		Test o4 = o1.foo(o2, o3, args.length);
		o4.f2 = new Test();
	}
	
	Test foo(Test p1, Test p2, int val) {
		Test a1 = new Test();
		if(val == 0) {
			a1.f1 = new Test();
		} else if (val == 1 ) {
			a1.f1 = new Child();
		} else {
			a1.f1 = new SecondChild();
		}
		Test o5 = new Child();
		a1.f1.f2= new Test();
		o5.f1 = o5.bar();
		p2.f1 = new Test();
		return o5.f1;
	}

	Test bar() {
		return new Test();
	}


}

class Child extends Test {
	Test foo(Test p1, Test p2, int val ) {
		return new Test();
	}
}

class SecondChild extends Test {
	Test foo(Test p1, Test p2, int val ) {
		return new Test();
	}
}