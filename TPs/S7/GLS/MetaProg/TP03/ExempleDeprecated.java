@Deprecated
class AA { }

class BB {
	@Deprecated
	public void m() {
		System.out.println("BB.m();");
}	}

public class ExempleDeprecated {
	void m1() {
		AA a = new AA();
		BB b = new BB();
		b.m();
	}

	@SuppressWarnings("deprecation")
	void m2() {
		AA a = new AA();
		BB b = new BB();
		b.m();
}	}
