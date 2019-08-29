package prelude.JML
;
/** representation of the EventB type ID (the identity relation)
 * @author Tim Wahls
 * @version 11/23/2011
 * @version 12/20/2011
 */

import org.jmlspecs.models.JMLEqualsBag;
import org.jmlspecs.models.JMLEqualsEqualsPair;
import org.jmlspecs.models.JMLEqualsSequence;
import org.jmlspecs.models.JMLEqualsSet;
import org.jmlspecs.models.JMLEqualsSetEnumerator;
import org.jmlspecs.models.JMLEqualsToEqualsMap;
import org.jmlspecs.models.JMLEqualsToEqualsRelationEnumerator;
import org.jmlspecs.models.JMLEqualsToEqualsRelationImageEnumerator;
import org.jmlspecs.models.JMLEqualsValuePair;
import org.jmlspecs.models.JMLIterator;
import org.jmlspecs.models.JMLValueSet;

public class ID<E> extends BRelation<E, E> {
	public ID() {}
		
	/*@ also assignable \nothing;
	    ensures \result <==> true;
	 */
	public boolean isaFunction() {
		return true;
	}
	
	/*@ also assignable \nothing;
        ensures \result.has(key) && \result.int_size() == 1;
     */
	public BSet<E> elementImage(E key) {
		return BSet.singleton(key);
	}

	/*@ also assignable \nothing;
        ensures \result.equals(keys);
     */
	public BSet<E> image(BSet<E> keys) {
		return keys;
	}
	
	/*@ also assignable \nothing;
    ensures \result.equals(this);
 */
	public BRelation<E, E> inverse() {
		return this;
	}
	
	/*@ also assignable \nothing;
        ensures \result.has(value) && \result.int_size() == 1;
     */
	public BSet<E> inverseElementImage(E value) {
		return new BSet<E>(value);
	}

	/*@ also assignable \nothing;
        ensures \result.equals(values);
     */
	public BSet<E> inverseImage(BSet<E> values) {
		return values;
	}
	
	/*@ also assignable \nothing;
        ensures \result <==> true;
     */
	public boolean isDefinedAt(E key) {
		return true;
	}
	
	/*@ also public exceptional_behavior
	      assignable \nothing;
          signals (UnsupportedOperationException);
     */
	public BRelation<E, E> add(E key, E value) {
		throw new UnsupportedOperationException("Error: cannot add to the identity relation.");
	}
	
	/*@ also public exceptional_behavior
          assignable \nothing;
          signals (UnsupportedOperationException);
     */
	public BRelation<E, E> insert(JMLEqualsEqualsPair<E, E> pair) {
		throw new UnsupportedOperationException("Error: cannot add to the identity relation.");
	}
	
	/*@ also public exceptional_behavior
          assignable \nothing;
          signals (UnsupportedOperationException);
     */
	public int int_size() {
		throw new UnsupportedOperationException("Error: the identity relation is infinite.");
	}
	
	/*@ also assignable \nothing;
	    ensures \result <==> key.equals(value);
	 */
	public boolean has(E key, E value) {
		return key.equals(value);
	}

	/*@ also assignable \nothing;
        ensures \result <==> pair.key.equals(pair.value);
     */
	public boolean has(JMLEqualsEqualsPair<E, E> pair) {
		return pair.key.equals(pair.value);
	}

	/*@ also assignable \nothing;
	    ensures \result <==> false;
	 */
	public boolean isEmpty() {
		return false;
	}
		
	/*@ also requires !(obj instanceof ID);
	      assignable \nothing;
	      ensures \result <==> false;
	    also requires obj instanceof ID;
	      assignable \nothing;
	      ensures \result <==> true;
	 */
	public boolean equals(Object obj) {
		return obj instanceof ID;
	}
	
	/*@ also assignable \nothing;
	    ensures \result == "ID".hashCode();
	 */
	public int hashCode() {
		return "ID".hashCode();
	}
	
	/*@ also assignable \nothing;
        ensures (\forall E e; \result.has(e));
     */
	public BSet<E> domain() {
		throw new UnsupportedOperationException("Error: cannot find the domain of the identity relation.");
	}
	
	/*@ also assignable \nothing;
       ensures (\forall E e; \result.has(e));
     */
	public BSet<E> range() {
		throw new UnsupportedOperationException("Error: cannot find the range of the identity relation.");
	}
	
	/*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair; \result.has(pair) <==> 
          pair.key.equals(pair.value) && !pair.key.equals(key));
     */
	public BRelation<E, E> removeFromDomain(E key) {
		throw new UnsupportedOperationException("Error: cannot remove from the identity relation.");
	}
	
	/*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair; \result.has(pair) <==> 
          pair.key.equals(pair.value) && !(pair.key.equals(key) && pair.value.equals(value)));
     */
	public BRelation<E, E> remove(E key, E value) {
		throw new UnsupportedOperationException("Error: cannot remove from the identity relation.");
	}
	
	/*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair2; \result.has(pair2) <==> 
          pair2.key.equals(pair2.value) && !(pair2.equals(pair)));
     */
	public BRelation<E, E> remove(JMLEqualsEqualsPair<E, E> pair) {
		throw new UnsupportedOperationException("Error: cannot remove from the identity relation.");
	}
	
	/*@ also assignable \nothing;
	    ensures \result.equals(otherRel);
	 */
	public <D> BRelation<D, E> compose(BRelation<D, E> otherRel) {
		return otherRel;
	}
	
	/*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair; \result.has(pair) <==> 
          pair.key.equals(pair.value) || otherRel.has(pair));
     */
	public BRelation<E, E> union(JMLEqualsSet<JMLEqualsEqualsPair<E, E>> otherRel) {
		throw new UnsupportedOperationException("Error: cannot union with the identity relation.");
	}

	/*@ also assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<E, E> pair; \result.has(pair) <==>
	      otherRel.has(pair) && pair.key.equals(pair.value));
	 */
	public BRelation<E, E> intersection(JMLEqualsSet<JMLEqualsEqualsPair<E, E>> otherRel) {
		BRelation<E, E> res = new BRelation<E, E>();
		for (JMLEqualsEqualsPair<E, E> pair : otherRel) {
			if (pair.key.equals(pair.value)) {
				res = res.insert(pair);
			}
		}
		return res;
	}

	/*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair; \result.has(pair) <==> 
          pair.key.equals(pair.value) && !otherRel.has(pair));
     */
	public BRelation<E, E> difference(JMLEqualsSet<JMLEqualsEqualsPair<E, E>> otherRel) {
		throw new UnsupportedOperationException("Error: cannot remove from the identity relation.");
	}
	
	/*@ also assignable \nothing;
        ensures (\forall E e; dom.has(e); \result.has(e, e));
     */
	public BRelation<E, E> restrictDomainTo(BSet<E> dom) {
		return Utils.cross(dom, dom);
	}
	
	/*@ also assignable \nothing;
        ensures (\forall E e; ran.has(e); \result.has(e, e));
     */
	public BRelation<E, E> restrictRangeTo(BSet<E> ran) {
		return Utils.cross(ran, ran);
	}
	
	/*@ also assignable \nothing;
	    ensures \result.equals("ID".toString());
	 */
	public String toString() {
		return "ID";
	}
	
	/*@ also public exceptional_behavior
          assignable \nothing;
          signals (UnsupportedOperationException);
     */
	public /*@ non_null @*/
	JMLEqualsToEqualsRelationEnumerator<E, E> associations() {
		throw new UnsupportedOperationException("Error: cannot iterate over the identity relation.");
	}

	/*@ also public exceptional_behavior
          assignable \nothing;
          signals (UnsupportedOperationException);
     */
	public JMLIterator<JMLEqualsEqualsPair<E, E>> iterator() {
		throw new UnsupportedOperationException("Error: cannot iterate over the identity relation.");
	}
	
	/*@ also assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<E, E> pair; this.has(pair) <==> \result.has(pair.key));
	 */
    public /*@ non_null @*/ BSet<JMLEqualsEqualsPair<E, E>> toSet() {
		throw new UnsupportedOperationException("Error: a set cannot contain the identity relation.");
    }

	/*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair; this.has(pair) <==> \result.has(pair.key));
     */
    public /*@ non_null @*/ JMLEqualsBag<JMLEqualsEqualsPair<E, E>> toBag() {
		throw new UnsupportedOperationException("Error: a bag cannot contain the identity relation.");
    }
    
	/*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair; this.has(pair) <==> \result.has(pair.key));
     */
    public /*@ non_null @*/ JMLEqualsSequence<JMLEqualsEqualsPair<E, E>> toSequence() {
		throw new UnsupportedOperationException("Error: a sequence cannot contain the identity relation.");
    }

	/*@ also assignable \nothing;
        ensures (\forall E e; \result.has(new JMLEqualsValuePair<E, JMLEqualsSet<E>>(e, new BSet<E>(e))));
     */
    public /*@ non_null @*/ JMLValueSet<JMLEqualsValuePair<E, JMLEqualsSet<E>>> imagePairSet() {
		throw new UnsupportedOperationException("Error: cannot iterate over the identity relation.");
    }
    
	/*@ also public exceptional_behavior
          assignable \nothing;
          signals (UnsupportedOperationException);
     */
    public /*@ non_null @*/
      JMLEqualsToEqualsRelationImageEnumerator<E, E> imagePairs() {
		throw new UnsupportedOperationException("Error: cannot iterate over the identity relation.");
    }

	/*@ also public exceptional_behavior
          assignable \nothing;
          signals (UnsupportedOperationException);
     */
    public /*@ non_null @*/ JMLEqualsSetEnumerator<E> domainElements()
    {
    	throw new UnsupportedOperationException("Error: cannot iterate over the identity relation.");
    }
    
	/*@ also public exceptional_behavior
          assignable \nothing;
          signals (UnsupportedOperationException);
     */
    public /*@ non_null @*/ JMLEqualsSetEnumerator<E> rangeElements()
    {
		throw new UnsupportedOperationException("Error: cannot iterate over the identity relation.");
    }

    /*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair; \result.has(pair) <==> pair.key.equals(pair.value));
     */
    public JMLEqualsToEqualsMap<E, E> toFunction() {
		throw new UnsupportedOperationException("Error: a function cannot contain the identity relation.");
    }
    
    /*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair; \result.has(pair) <==> 
          pair.key.equals(pair.value) && !domain.has(pair.key));
     */
    public BRelation<E, E> domainSubtraction(BSet<E> domain) {
		throw new UnsupportedOperationException("Error: cannot remove from the identity relation.");
    }
    
    /*@ also assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<E, E> pair; \result.has(pair) <==> 
          pair.key.equals(pair.value) && !range.has(pair.value));
     */
    public BRelation<E, E> rangeSubtraction(BSet<E> range) {
		throw new UnsupportedOperationException("Error: cannot remove from the identity relation.");
    }
 
    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
    public boolean isTotal(BSet<E> domain, BSet<E> range) {
    	return true;
    }
    
    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
    public boolean isSurjective(BSet<E> domain, BSet<E> range) {
    	return true;
    }	
    
    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
    public boolean isTotalSurjective(BSet<E> domain, BSet<E> range) {
    	return true;
    }
    
    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
	public boolean isFunction(BSet<E> dom, BSet<E> ran) {
    	return true;
	}
	
    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
	public boolean isRelation(BSet<E> dom, BSet<E> ran) {
    	return true;
	}

    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
	public boolean isTotalFunction(BSet<E> dom, BSet<E> ran) {
    	return true;
	}
	
    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
	public boolean isPartialInjection(BSet<E> dom, BSet<E> ran) {
    	return true;
	}
	
    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
	public boolean isTotalInjection(BSet<E> dom, BSet<E> ran) {
    	return true;
	}
	
    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
	public boolean isPartialSurjection(BSet<E> dom, BSet<E> ran) {
    	return true;
	}

    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
	public boolean isTotalSurjection(BSet<E> dom, BSet<E> ran) {
    	return true;
	}
	
    /*@ also assignable \nothing;
        ensures \result <==> true;
     */
	public boolean isInjection(BSet<E> dom, BSet<E> ran) {
    	return true;
	}
    
	/*@ also assignable \nothing;
        ensures \result.equals(otherRel);
     */
	public <D> BRelation<E, D> backwardCompose(BRelation<E, D> otherRel) {
		return otherRel;
	}
	
	/*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
	public BRelation<E, E> override(BRelation<E, E> other) {
		throw new UnsupportedOperationException("Error: cannot remove from the identity relation.");
	}
	
	/*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
	public <D> BRelation<E, JMLEqualsEqualsPair<E, D>> parallel(BRelation<E, D> other) {
		throw new UnsupportedOperationException("Error: cannot parallel the identity relation.");
	}
	
	/*@ also public exceptional_behavior
        assignable \nothing;
        signals (UnsupportedOperationException);
     */
	public <K1, V1> BRelation<JMLEqualsEqualsPair<E, K1>, JMLEqualsEqualsPair<E, V1>> directProd(BRelation<K1, V1> other) {
		throw new UnsupportedOperationException("Error: cannot direct product with the identity relation.");
	}

	/*@ also assignable \nothing;
        ensures \result.equals(key);
    */
	public E apply(E key) {
		return key;
	}
	
	/*@ also assignable \nothing;
	    ensures (\forall BSet<JMLEqualsEqualsPair<E, E>> s; \result.has(s) <==> s.isSubset(this));
	 */
	public BSet<BSet<JMLEqualsEqualsPair<E, E>>> pow() {
		throw new UnsupportedOperationException("Error: cannot compute powerset of the identity relation.");
	}
	
	/*@ also assignable \nothing;
        ensures (\forall BSet<JMLEqualsEqualsPair<E, E>> s; \result.has(s) <==> s.isSubset(this) && !s.isEmpty());
     */
	public BSet<BSet<JMLEqualsEqualsPair<E, E>>> pow1() {
		throw new UnsupportedOperationException("Error: cannot compute powerset of the identity relation.");
	}

	/*@ also assignable \nothing;
	    ensures \result <==> false;
	 */
	public boolean finite() {
		return false;
	}
	
	/** inherited specs for containsAll, sub and supersets and choose are correct */
	
	public boolean containsAll(java.util.Collection<JMLEqualsEqualsPair<E, E>> col) {
		for (JMLEqualsEqualsPair<E, E> pair : col) {
			if (!pair.key.equals(pair.value)) return false;
		}
		return true;
	}
	
	public boolean isSubset(JMLEqualsSet<JMLEqualsEqualsPair<E, E>> other) {
		if (other instanceof ID) {
			return true;
		} else {
			return false;
		}
	}

	public boolean isProperSubset(JMLEqualsSet<JMLEqualsEqualsPair<E, E>> other) {
		return false;
	}
	
	public boolean isSuperset(JMLEqualsSet<JMLEqualsEqualsPair<E, E>> other) {
		if (other instanceof ID) return true;
		for (JMLEqualsEqualsPair<E, E> pair : other) {
			if (!pair.key.equals(pair.value)) return false;
		}
		return true;
	}

	public boolean isProperSuperset(JMLEqualsSet<JMLEqualsEqualsPair<E, E>> other) {
		if (other instanceof ID) return false;
		return isSuperset(other);
	}

	public JMLEqualsEqualsPair<E, E> choose() {
		throw new UnsupportedOperationException("Error: cannot choose from the identity relation.");
	}

}
