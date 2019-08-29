package prelude.JML;

/** representation of the EventB type INT as a JMLEqualsSet
 * @author Tim Wahls
 * @version 11/23/2011
 * @version 12/20/2011
 */

import org.jmlspecs.models.JMLEqualsBag;
import org.jmlspecs.models.JMLEqualsSequence;
import org.jmlspecs.models.JMLEqualsSet;
import org.jmlspecs.models.JMLIterator;

public /*@ pure */ class INT extends BSet<Integer> {
	public static final INT instance = new INT();
	private java.util.Random rand = new java.util.Random();
	
//	/*@ public static initially (\forall int iv; INT.instance.has(iv)); */
	
	private INT() {}
	
	/*@ also assignable \nothing;
	    ensures \result <==> obj instanceof Integer;
	 */
	public boolean has(Object obj) {
		return obj instanceof Integer;
	}
	
	/*@ also assignable \nothing;
        ensures \result <==> (\forall Integer i; c.contains(i); this.has(i));
     */
	public boolean containsAll(java.util.Collection<Integer> c) {
		return true;
	}
	
	/*@ also requires other instanceof BSet;
	    assignable \nothing;
        ensures \result <==> (\forall Integer i; this.has(i) <==> ((BSet) other).has(i));
     */
	public boolean equals(Object other) {
		return other instanceof INT;
	}
	
	/*@ also assignable \nothing;
        ensures \result <==> false;
     */
    public boolean isEmpty() {
    	return false;
    }
    
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
    public int int_size() {
        throw new UnsupportedOperationException("Error: size of the integers not representable");
    }  
    
    /*@ also assignable \nothing;
        ensures \result == "INT".hashCode();
     */
    public int hashCode() {
    	return "INT".hashCode();
    }
    
    /* inherited specifications should be correct for all set operations */
    
    public boolean isSubset(/*@ non_null @*/ JMLEqualsSet<Integer> s2) {
    	return s2 instanceof INT;
    }
    
    public boolean isProperSubset(/*@ non_null @*/ JMLEqualsSet<Integer> s2) {
    	return false;
    }
    
    public  boolean isSuperset(/*@ non_null @*/ JMLEqualsSet<Integer> s2) {
    	return true;
    }
    
    public boolean isProperSuperset(/*@ non_null @*/ JMLEqualsSet<Integer> s2) {
    	return !(s2 instanceof INT);
    }
    
    public Integer choose() {
    	return rand.nextInt();
    }
    
    public Object clone() {
    	return this;
    }
    
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
    public BSet<Integer> insert(Integer i) {
    	throw new UnsupportedOperationException("Error: can't insert into the integers");
    }
    
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
    public BSet<Integer> remove(Integer i) {
    	throw new UnsupportedOperationException("Error: can't remove from the integers");
    }
    
    public BSet<Integer> intersection(JMLEqualsSet<Integer> s2) {
    	if (s2 instanceof BSet) {
    		return (BSet<Integer>) s2;
    	} else {
    		return new BSet<Integer>(s2);
    	}
    }
	 
    public BSet<Integer> union(JMLEqualsSet<Integer> s2) {
    	return this;
    }
    
    public BSet<Integer> difference(JMLEqualsSet<Integer> s2) {
    	if (s2 instanceof INT) {
    		return new BSet<Integer>();
    	} else {
    		throw new UnsupportedOperationException("Error: difference from the integers is infinite.");
    	}
    }
    
    /*@ also assignable \nothing;
        ensures \result.equals("INT");
     */
    public String toString() {
    	return "INT";
    }
    
    /*@ also assignable \nothing;
        ensures (\forall int i; \result.has(i));
     */
	public JMLEqualsBag<Integer> toBag() {
    	throw new UnsupportedOperationException("Error: a bag cannot contain the integers.");		
	}
    
    /*@ also assignable \nothing;
        ensures (\forall int i; \result.has(i));
     */
	public JMLEqualsSequence<Integer> toSequence() {
    	throw new UnsupportedOperationException("Error: a sequence cannot contain the integers.");		
	}
	
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
	public Object [] toArray() {
    	throw new UnsupportedOperationException("Error: an array cannot contain the integers.");		
	}
	
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
	public JMLIterator<Integer> iterator() {
	   	throw new UnsupportedOperationException("Error: the integers are not iterable.");		
	}

	/*@ also assignable \nothing;
	    ensures \result <==> false;
	 */
    public boolean finite() {
    	return false;
    }
    
    /*@ also assignable \nothing;
        ensures (\forall BSet<Integer> es; \result.has(es));
     */
    public BSet<BSet<Integer>> pow() {
    	throw new UnsupportedOperationException("Error: can't compute POW(INT).");    	
    }
    
    /*@ also assignable \nothing;
        ensures (\forall BSet<Integer> es; !es.isEmpty(); \result.has(es));
     */
    public BSet<BSet<Integer>> pow1() {
    	throw new UnsupportedOperationException("Error: can't compute POW1(INT).");    	
    }
    
    /*@ also assignable \nothing;
        ensures \result <==> parts.length == 1 && parts[0] instanceof INT;
     */
    public boolean partition(BSet<Integer> ... parts) {
    	return parts.length == 1 && parts[0] instanceof INT;
    }
    
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
    public Integer max() {
    	throw new UnsupportedOperationException("Error: can't compute max of INT.");    	    	
    }
    
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
    public Integer min() {
    	throw new UnsupportedOperationException("Error: can't compute min of INT.");    	    	
    }
}
