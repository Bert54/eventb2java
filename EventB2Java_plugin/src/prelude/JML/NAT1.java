package prelude.JML;

/** representation of the EventB type NAT1 as a JMLEqualsSet
 * @author Tim Wahls
 * @version 11/23/2011
 * @version 12/20/2011
 */

import org.jmlspecs.models.JMLEqualsBag;
import org.jmlspecs.models.JMLEqualsSequence;
import org.jmlspecs.models.JMLEqualsSet;
import org.jmlspecs.models.JMLIterator;

public class NAT1 extends BSet<Integer> {
	public static final NAT1 instance = new NAT1();
	
	private NAT1() {}
	
	
	/*@ also assignable \nothing;
        ensures \result <==> obj instanceof Integer && ((Integer) obj) > 0;
     */
	public boolean has(Object obj) {
		return INT.instance.has(obj) && ((Integer) obj) > 0;
	}
	
	/*@ also assignable \nothing;
        ensures \result <==> (\forall Integer i; c.contains(i); this.has(i));
     */
	public boolean containsAll(java.util.Collection<Integer> c) {
		for (Integer i : c) {
			if (i <= 0) return false;
		}
		return true;
	}
	
	/*@ also assignable \nothing;
        ensures \result <==> obj instanceof BSet && (\forall Integer i; this.has(i) <==> ((BSet) obj).has(i));
     */
	public boolean equals(Object obj) {
		return obj instanceof NAT1;
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
        throw new UnsupportedOperationException("Error: size of the NATs not representable");
    }  
    
    /*@ also assignable \nothing;
        ensures \result == "NAT1".hashCode();
     */
    public int hashCode() {
    	return "NAT1".hashCode();
    }
    
    /** inherited specification should be correct for all set operations */
    
    public boolean isSubset(/*@ non_null @*/ JMLEqualsSet<Integer> s2) {
    	return s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1;
    }
    
    public boolean isProperSubset(/*@ non_null @*/ JMLEqualsSet<Integer> s2) {
    	return s2 instanceof INT || s2 instanceof NAT;
    }
    
    public  boolean isSuperset(/*@ non_null @*/ JMLEqualsSet<Integer> s2) {
    	if (s2 instanceof INT || s2 instanceof NAT) {
    		return false;
    	} else if (s2 instanceof NAT1) {
    		return true;
    	} else  {
    		for (Integer i : s2) {
    			if (i <= 0) return false;
    		}
    		return true;
    	}
    }

    public boolean isProperSuperset(/*@ non_null @*/ JMLEqualsSet<Integer> s2) {
    	if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {
    		return false;
    	} else {
    		for (Integer i : s2) {
    			if (i <= 0) return false;
    		}
    		return true;   		
    	}
    }

    public Integer choose() {
    	return 0;
    }

    public Object clone() {
    	return this;
    }
    
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
    public BSet<Integer> insert(Integer i) {
    	throw new UnsupportedOperationException("Error: can't insert into the NAT1s");
    }
    
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
    public BSet<Integer> remove(Integer i) {
    	throw new UnsupportedOperationException("Error: can't remove from the NAT1s");
    }
    
    public BSet<Integer> intersection(JMLEqualsSet<Integer> s2) {
    	if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {
    		return this;
    	} else {
    		BSet<Integer> res = new BSet<Integer>();
    		for (Integer i : s2) {
    			if (i > 0) {
    				res = res.insert(i);
    			}
    		}
    		return res;
    	}
     }
	 
    public BSet<Integer> union(JMLEqualsSet<Integer> s2) {
    	if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {
    		return (BSet<Integer>) s2;
    	} else {
    		for (Integer i : s2) {
    			if (i <= 0) {
    				throw new UnsupportedOperationException("Error: can't union with the NATs");
    			}
    		}
        	return this;
    	}
    }

    
    public BSet<Integer> difference(JMLEqualsSet<Integer> s2) {
    	if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {
    		return new BSet<Integer>();
    	} else {
    		throw new UnsupportedOperationException("Error: difference from the integers is infinite.");
    	}
    }
    
    /*@ also assignable \nothing;
        ensures \result.equals("NAT1");
     */
    public String toString() {
    	return "NAT1";
    }

    
    /*@ also assignable \nothing;
        ensures (\forall Integer i; this.has(i) <==> \result.has(i));
     */
	public JMLEqualsBag<Integer> toBag() {
    	throw new UnsupportedOperationException("Error: a bag cannot contain the NAT1s.");		
	}
    
    /*@ also assignable \nothing;
        ensures (\forall Integer i; this.has(i) <==> \result.has(i));
     */
	public JMLEqualsSequence<Integer> toSequence() {
    	throw new UnsupportedOperationException("Error: a sequence cannot contain the NAT1s.");		
	}
	
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
	public Object [] toArray() {
    	throw new UnsupportedOperationException("Error: an array cannot contain the NAT1s.");		
	}
	
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
	public JMLIterator<Integer> iterator() {
	   	throw new UnsupportedOperationException("Error: the NAT1s are not iterable.");		
	}

	/*@ also assignable \nothing;
	    ensures \result <==> false;
	 */
    public boolean finite() {
    	return false;
    }
    
    /*@ also assignable \nothing;
        ensures (\forall BSet<Integer> es; es.isSubset(this) <==> \result.has(es));
     */
    public BSet<BSet<Integer>> pow() {
    	throw new UnsupportedOperationException("Error: can't compute POW(NAT1).");    	
    }
    
    /*@ also assignable \nothing;
        ensures (\forall BSet<Integer> es; es.isSubset(this) && !es.isEmpty() <==> \result.has(es));
     */
    public BSet<BSet<Integer>> pow1() {
    	throw new UnsupportedOperationException("Error: can't compute POW1(NAT1).");    	
    }
    
    /*@ also assignable \nothing;
        ensures \result <==> parts.length == 1 && parts[0] instanceof NAT1;
     */
    public boolean partition(BSet<Integer> ... parts) {
    	return (parts.length == 1 && parts[0] instanceof NAT1);
    }
    
    /*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
    public Integer max() {
    	throw new UnsupportedOperationException("Error: can't compute max of NAT1.");    	    	
    }
    
    /* also assignable \nothing;
       ensures \result == 1;
     */
    public Integer min() {
    	return 1;    	    	
    }
}
