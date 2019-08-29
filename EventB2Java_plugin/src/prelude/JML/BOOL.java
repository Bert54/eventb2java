package prelude.JML;

/** a class to represent type BOOL as a set in JML 
 * @author Tim Wahls
 * @version 11/23/2011
 * @version 12/20/2011
 */

public class BOOL extends BSet<Boolean> {
	public static final BOOL instance = new BOOL();
	
	/*@ public static initially BOOL.instance.has(true) && BOOL.instance.has(false); */
	
	private BOOL() {
		elems = elems.insert(true);
		elems = elems.insert(false);
	}
}
