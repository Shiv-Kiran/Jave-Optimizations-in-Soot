// Testcase 5:
// Handling Arrays and list

import java.util.ArrayList;
import java.util.List;

class Test {
	Test f1;
	Test f2;

	public static void main(String[] args) {
		Test[] arr1 = new Test[10];
		Test[] arr2 = new Test[5];
		for (int i = 0; i < 10; i++) {
			arr1[i] = new Test();
		}
		arr2[0] = new Test();
		arr2[1] = new Test();
		arr2[2] = new Test();
		arr2[3] = new Test();
		arr2[4] = new Test();
		arr1[0].foo(arr2[0]);
	}

	void foo(Test p1) {
		System.out.println(p1);
	}
}
