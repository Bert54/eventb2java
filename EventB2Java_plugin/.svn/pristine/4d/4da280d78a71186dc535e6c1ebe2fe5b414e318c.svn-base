package prelude.JML;

/** utility methods for sets and relations
 * 
 * @author Tim Wahls
 * @version 11/23/2011
 * @version 12/20/2011
 */

import org.jmlspecs.models.JMLEqualsEqualsPair;

public class Utils {
	
	/*@ assignable \nothing;
	    ensures (\forall E e; \result.has(e) <==> 
	      (\exists int i; 0 <= 1 && i < elems.length; elems[i].equals(e)));
	 */
	public static <E> BSet<E> extension(E ... elems) {
		BSet<E> res = new BSet<E>();
		for (E e : elems) {
			res = res.insert(e);
		}
		return res;
	}
	
	/*@ assignable \nothing;
	    ensures (\forall E e; \result.has(e) <==>
	      (\exists int i; 0 <= 1 && i < sets.length; sets[i].has(e)));
	 */
	public static <E> BSet<E> union(BSet<E> ... sets) {
		BSet<E> res = new BSet<E>();
		for (BSet<E> set : sets) {
			res = res.union(set);
		}
		return res;
	}
	
	/*@ assignable \nothing;
	    ensures \result.isEmpty();
	 */
	public static <E> BSet<E> union() {
		return new BSet<E>();
	}
	
	/*@ assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<K, V> e; \result.has(e) <==>
          (\exists int i; 0 <= 1 && i < sets.length; sets[i].has(e)));
     */
	public static <K, V> BRelation<K, V> union(BRelation<K, V> ... sets) {
		BRelation<K, V> res = new BRelation<K, V>();
		for (BRelation<K, V> set : sets) {
			res = res.union(set);
		}
		return res;
	}
	
	/*@ public exceptional_behavior
	    requires true;
	    assignable \nothing;
	    signals (IllegalStateException);
	 */
	public static <E> BSet<E> intersection() {
		throw new IllegalStateException("Error: generalized intersection over 0 sets.");
	}
	
	/*@ assignable \nothing;
        ensures (\forall E e; \result.has(e) <==>
          (\forall int i; 0 <= 1 && i < sets.length; sets[i].has(e)));
     */
	public static <E> BSet<E> intersection(BSet<E> ... sets) {
		BSet<E> res = sets[0];
		for (int i = 1; i < sets.length; i++) {
			res = res.intersection(sets[i]);
		}
		return res;
	}
	
	/*@ assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<K, V> e; \result.has(e) <==>
          (\forall int i; 0 <= 1 && i < sets.length; sets[i].has(e)));
     */
	public static <K, V> BRelation<K, V> intersection(BRelation<K, V> ... sets) {
		BRelation<K, V> res = sets[0];
		for (int i = 1; i < sets.length; i++) {
			res = res.intersection(sets[i]);
		}
		return res;
	}

	/*@ assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<K, V> e; \result.has(e) <==>
	      domain.has(e.key) && range.has(e.value));
	 */
	public static <K, V> BRelation<K, V> cross(BSet<K> domain, BSet<V> range) {
		BRelation<K, V> res = new BRelation<K, V>();
		for (K key : domain) {
			for (V value : range) {
				res = res.add(key, value);
			}
		}
		return res;
	}
	
	/*TODO: JML specification*/
	public static <K> boolean partition(BSet<K> ... sets){
		if (sets.length == 0){
			return false;
		}else{
			if (sets.length == 1){
				return true;
			}	
		}
		boolean res = true;
		BSet<K> a = sets[0];
		//sets[0] = union(sets[1:])
		BSet<K> others = new BSet<K>();
		for (int i = 1; i < sets.length; i++){
			others = others.union(sets[i]);
		}
		res = a.equals(others);
		if (res){
			for (int i = 1; i < sets.length-1; i++){
				for (int j = i+1; j < sets.length; j++){
					if (!sets[i].intersection(sets[j]).isEmpty()){
						return false;
					}
				}
			}
		}
		return res;
	}
	
	public static boolean implication(boolean p, boolean q){
		return (!p || q);
	}
	
	public static boolean bi_implication(boolean p, boolean q){
		return (p && q) || (!p && !q);
	}
}
