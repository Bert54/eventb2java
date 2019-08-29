package prelude.JML;

/** a class to construct intervals in JML 
 * @author Tim Wahls
 * @version 11/23/2011
 * @version 12/20/2011
 */

public class Range extends BSet<Integer> {
	
	/*@ assignable elems;
	    ensures (\forall int i; low <= i && i <= hi; elems.has(i)) 
	         && elems.int_size() == (hi - low) + 1;
	 */
	public Range(int low, int hi) {
		for (int i = low; i <= hi; i++) {
			elems = elems.insert(i);
		}
	}
}
