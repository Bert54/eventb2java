package prelude.EB;

public class Test {
	
	public static void main(String[] args) {		
		Pair p1 = new Pair(1,2);
		Pair p2 = new Pair(1,3);
		
		BSet<Pair> s1 = new BSet<Pair>();
		s1.add(p1);
		
		BSet<Pair> s2 = new BSet<Pair>();
		s2.add(p2);
		
		BRelation r1 = new BRelation(s1);
		BRelation r2 = new BRelation(s2);

		boolean b = r1.equals(r2);
		
		System.out.println(b);
	}

}
