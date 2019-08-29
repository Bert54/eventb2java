package prelude.JML;

import org.jmlspecs.models.JMLEqualsBag;
import org.jmlspecs.models.JMLEqualsSequence;
import org.jmlspecs.models.JMLEqualsSet;
import org.jmlspecs.models.JMLIterator;
import org.jmlspecs.models.JMLNoSuchElementException;

/** a class to represent B sets in JML 
 * @author Tim Wahls
 * @version 11/23/2011
 * @version 12/20/2011
 */

public class BSet<E> extends JMLEqualsSet<E> {
	protected /*@ spec_public */ JMLEqualsSet<E> elems;
	
	/*@ public static invariant EMPTY.int_size() == 0; */
	
	public static BSet EMPTY = new BSet();
	
	/*@ assignable \nothing;
	    ensures \result.int_size() == 1 && \result.has(elem);
	 */
	public static <F> BSet<F> singleton(F elem) {
		return new BSet<F>().insert(elem);
	}
	
	/*@ assignable elems;
	    ensures elems.isEmpty();
	 */
	public BSet() {
		elems = new JMLEqualsSet<E>();
	}
	
	/** for implementing set extension */
	/*@ assignable elems;
	    ensures elems.equals(JMLEqualsSet.convertFrom(els));
	 */
	public BSet(E ... els) {
		this();
		for (E e : els) {
			elems = elems.insert(e);
		}
	}
	
	/*@ assignable elems;
	    ensures this.elems.equals(elems);
	 */
	public BSet(JMLEqualsSet<E> elems) {
        if (elems instanceof BSet) {
            this.elems = ((BSet<E>) elems).elems;
        } else {
            this.elems = elems;
        }
    }

	/*@ assignable elems;
	    ensures elems.equals(\old(elems).insert(elem));
	 */
	public BSet<E> insert(E elem) {
		JMLEqualsSet<E> newElems = elems.insert(elem);
		return new BSet<E>(newElems);
	}
	
	/*@ assignable \nothing;
	    ensures \result <==> elems.has(obj);
	 */
	public boolean has(Object obj) {
		return elems.has(obj);
	}
	
	/*@ assignable \nothing;
	    ensures \result <==> (\forall E e; col.contains(e); this.has(e));
	 */
	public boolean containsAll(java.util.Collection<E> col) {
		if (col instanceof INT || col instanceof NAT || col instanceof NAT1) {
			return false;
		} else {
			return elems.containsAll(col);
		}
	}

	/*@ also assignable \nothing;
	    ensures \result <==> obj instanceof BSet && 
	      (\forall E e; ((BSet) obj).has(e) <==> this.has(e));
	 */
	public boolean equals(Object obj) {
        if (obj instanceof BRelation) {
                return elems.equals(((BRelation) obj).toSet().elems);
        } else {
                return elems.equals(obj);
        }
	}

	
	/*@ also requires !(this instanceof NAT || this instanceof NAT1 || this instanceof INT);;
	    assignable \nothing;
	    ensures \result == elems.int_size();
	 */
	public int int_size() {
		return elems.int_size();
	}
	
	/*@ also requires !(this instanceof NAT || this instanceof NAT1 || this instanceof INT);
	    assignable \nothing;
        ensures \result == elems.isEmpty();
	 */
	public boolean isEmpty() {
		return elems.isEmpty();
	}

	/*@ also requires !(this instanceof NAT || this instanceof NAT1 || this instanceof INT);
	    assignable \nothing;
        ensures \result == elems.hashCode();
	 */
	public int hashCode() {
		return elems.hashCode();
	}
	
	/*@ also assignable \nothing;
        ensures \result <==> (\forall E e; this.has(e); s2.has(e));
	 */
	public boolean isSubset(JMLEqualsSet<E> s2) {
		if (s2 instanceof INT) {
			return true;
		} else if (s2 instanceof NAT || s2 instanceof NAT1) {
			for (Object obj : this) {
				Integer i = (Integer) obj;
				if (i < 0) return false;
				else if (i == 0 && s2 instanceof NAT1) return false;
			}
			return true;
		} else {
			return elems.isSubset(s2);
		}
	}
	
	/*@ also assignable \nothing;
        ensures \result <==> this.isSubset(s2) && !this.equals(s2);
	 */
	public boolean isProperSubset(JMLEqualsSet<E> s2) {
		if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {
			return isSubset(s2);
		} else {
			return elems.isProperSubset(s2);
		}
	}
	
	/*@ also assignable \nothing;
	    ensures \result <==> s2.isSubset(this);
	 */
	public boolean isSuperset(JMLEqualsSet<E> s2) {
		return s2.isSubset(this);
	}
	
	/*@ also assignable \nothing;
	    ensures \result <==> s2.isProperSubset(this);
	 */
	public boolean isProperSuperset(JMLEqualsSet<E> s2) {
		return s2.isProperSubset(this);
	}
	
	/*@ also public normal_behavior
	      assignable \nothing;
	      ensures this.has(\result);
	    also public exceptional_behavior
	      requires this.isEmpty();
	      signals (JMLNoSuchElementException);
	 */
	public E choose() {
		return elems.choose();
	}
	
	/*@ also assignable \nothing;
	    ensures \result.equals(this) && \fresh(\result);
	 */
	public Object clone() {
		return new BSet<E>(elems);
	}
	
	/*@ also assignable \nothing;
	    ensures (\forall E e; \result.has(e) <==> this.has(e) && !e.equals(elem));
	 */
	public BSet<E> remove(E elem) {
		return new BSet<E>(elems.remove(elem));
	}
	
	/*@ also assignable \nothing;
	    ensures (\forall E e; \result.has(e) <==> this.has(e) || s2.has(e));
	 */
	public BSet<E> union(JMLEqualsSet<E> s2) {
		if (s2 instanceof INT) {
			return (BSet<E>) s2;
		} else if (s2 instanceof NAT || s2 instanceof NAT1) {
			for (Object obj : this) {
				Integer i = (Integer) obj;
				if (i < 0) throw new UnsupportedOperationException("Error: can't union with NAT.");
				else if (i == 0 && s2 instanceof NAT1) throw new UnsupportedOperationException("Error: can't union with NAT1.");
			}
			return (BSet<E>) s2;
		} else {
			return new BSet<E>(elems.union(s2));
		}
	}
	
	/*@ also assignable \nothing;
        ensures (\forall E e; \result.has(e) <==> this.has(e) && s2.has(e));
	 */
	public BSet<E> intersection(JMLEqualsSet<E> s2) {
		if (s2 instanceof INT) {
			return this;
		} else if (s2 instanceof NAT || s2 instanceof NAT1) {
			BSet<E> res = this;
			for (E obj : this) {
				Integer i = (Integer) obj;
				if (i < 0) res = res.remove(obj);
				else if (i == 0 && s2 instanceof NAT1) res = res.remove(obj);				
			}
			return res;
		} else {
			return new BSet<E>(elems.intersection(s2));
		}
	}
	
	/*@ also assignable \nothing;
        ensures (\forall E e; \result.has(e) <==> this.has(e) && !s2.has(e));
	 */
	public BSet<E> difference(JMLEqualsSet<E> s2) {
		if (s2 instanceof INT) {
			return new BSet<E>();
		} else if (s2 instanceof NAT || s2 instanceof NAT1) {
			BSet<E> res = this;
			for (E obj : this) {
				Integer i = (Integer) obj;
				if (i > 0) res = res.remove(obj);
				else if (i == 0 && s2 instanceof NAT) res = res.remove(obj);
			}
			return res;
		} else {
			return new BSet<E>(elems.difference(s2));
		}
	}
	
	/*@ also public exceptional_behavior
	    assignable \nothing;
	    signals (UnsupportedOperationException);
	 */
	public JMLEqualsSet<JMLEqualsSet<E>> powerSet() {
		throw new UnsupportedOperationException("Error: do not call powerSet through a BSet.");
	}
	
	/*@ also assignable \nothing;
	    ensures \result.equals(elems.toString());
	 */
	public String toString() {
		return elems.toString();
	}
	
	/*@ also assignable \nothing;
	    ensures \result.equals(elems.toBag());
	 */
	public JMLEqualsBag<E> toBag() {
		return elems.toBag();
	}
	
	/*@ also assignable \nothing;
	    ensures \result.equals(elems.toSequence());
	 */
	public JMLEqualsSequence<E> toSequence() {
		return elems.toSequence();
	}
	
	/*@ also assignable \nothing;
	    ensures \result.equals(elems.toArray());
	 */
	public Object [] toArray() {
		return elems.toArray();
	}
	
	/*@ also assignable \nothing;
	    ensures \result.equals(elems.iterator());
	 */
	public JMLIterator<E> iterator() {
		return elems.iterator();
	}
	
	/*@ assignable \nothing;
	    ensures (\forall BSet<E> es; \result.has(es) <==> es.isSubset(this));
	 */
	public BSet<BSet<E>> pow() {
		BSet<BSet<E>> res = new BSet<BSet<E>>();
		JMLEqualsSet<JMLEqualsSet<E>> pow = elems.powerSet();
		for (JMLEqualsSet<E> set : pow) {
			res = res.insert(new BSet<E>(set));
		}
		return res;
	}
	
	/*@ assignable \nothing;
        ensures (\forall BSet<E> es; \result.has(es) <==> es.isSubset(this) && !es.isEmpty());
     */
	public BSet<BSet<E>> pow1() {
		return pow().difference(new BSet<BSet<E>>().insert(new BSet<E>()));
	}
	
	/*@ assignable \nothing;
        ensures \result <==> !(this instanceof INT || this instanceof NAT || this instanceof NAT1);
     */
	public boolean finite() {
		return true;
	}

	/*@ assignable \nothing;
	    ensures \result <==> (\forall int i; 0 <= i && i < parts.length; 
	      !(\exists int j; 0 <= j && j < parts.length; i != j && !parts[i].intersection(parts[j]).isEmpty()))
	   && (\forall E e; this.has(e) <==> (\exists int i; 0 <= i && i < parts.length; parts[i].has(e))); 
	 */
	public boolean partition(BSet<E> ... parts) {
		if (parts.length == 0) return isEmpty();
		else {
			for (int i = 0; i < parts.length; i++) {
				for (int j = i + 1; j < parts.length; j++) {
					if (!parts[i].intersection(parts[j]).isEmpty()) {
						return false;
					}
				}
			}
		}
		return this.equals(prelude.JML.Utils.union(parts));
	}
	
	/*@ public normal_behavior
	      requires !this.isEmpty() && this.choose() instanceof Comparable;
	      assignable \nothing;
	      ensures (\forall E e; this.has(e); ((Comparable) \result).compareTo(e) >= 0);
	    also public exceptional_behavior
	      requires !this.isEmpty() && !(this.choose() instanceof Comparable);
	      assignable \nothing;
	      signals (ClassCastException);
	    also public exceptional_behavior
	      requires this.isEmpty();
	      assignable \nothing;
	      signals (java.util.NoSuchElementException);
	 */
	public E max() {
		try {
			JMLIterator<E> iter = elems.iterator();
			E max = iter.next();
			while (iter.hasNext()) {
				E next = iter.next();
				if (((Comparable<E>) max).compareTo(next) < 0) {
					max = next;
				}
			}
			return max;
		} catch (ClassCastException cce) {
			throw new UnsupportedOperationException("Error: cannot find the max of a set of elements that do not have a total order.");
		}
	}
	
	/*@ public normal_behavior
          requires !this.isEmpty() && this.choose() instanceof Comparable;
          assignable \nothing;
          ensures (\forall E e; this.has(e); ((Comparable) \result).compareTo(e) <= 0);
        also public exceptional_behavior
          requires !this.isEmpty() && !(this.choose() instanceof Comparable);
          assignable \nothing;
          signals (ClassCastException);
        also public exceptional_behavior
          requires this.isEmpty();
          assignable \nothing;
          signals (java.util.NoSuchElementException);
	 */
	public E min() {
		try {
			JMLIterator<E> iter = elems.iterator();
			E min = iter.next();
			while (iter.hasNext()) {
				E next = iter.next();
				if (((Comparable<E>) min).compareTo(next) > 0) {
					min = next;
				}
			}
			return min;
		} catch (ClassCastException cce) {
			throw new UnsupportedOperationException("Error: cannot find the max of a set of elements that do not have a total order.");
		}
	}
	
}
