package prelude.JML;

/** a class to represent B relations in JML 
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
import org.jmlspecs.models.JMLEqualsToEqualsRelation;
import org.jmlspecs.models.JMLEqualsToEqualsRelationEnumerator;
import org.jmlspecs.models.JMLEqualsToEqualsRelationImageEnumerator;
import org.jmlspecs.models.JMLEqualsValuePair;
import org.jmlspecs.models.JMLIterator;
import org.jmlspecs.models.JMLValueSet;
import org.jmlspecs.models.JMLNoSuchElementException;

public class BRelation<K, V> extends BSet<JMLEqualsEqualsPair<K, V>> {
	private /*@ spec_public */ JMLEqualsToEqualsRelation<K, V> elems;
	
	public static BRelation EMPTY = new BRelation();
	
	/*@ public static invariant EMPTY.int_size() == 0; */
	
	/*@ assignable elems;
	    ensures elems.isEmpty();
	 */
	public BRelation() {
		elems = new JMLEqualsToEqualsRelation<K, V>();
	}
	
	/*@ assignable this.elems;
	    ensures this.elems.equals(elems);
	 */
	BRelation(JMLEqualsToEqualsRelation<K, V> elems) {
		this.elems = elems;		
	}
	
	/*@ assignable this.elems;
    ensures this.elems.equals(elems);
	 */
	BRelation(BRelation<K, V> elems) {
		this.elems = elems.elems;		
	}
	
	/*@ assignable elems;
	    ensures (\forall K k; (\forall V v; elems.has(k, v) <==> 
	       (\exists int i; 0 <= i && i < pairs.length;
	          pairs[i].key.equals(k) && pairs[i].value.equals(v))));
	 */
	public BRelation(JMLEqualsEqualsPair<K, V> ... pairs) {
		this();
		for (JMLEqualsEqualsPair<K, V> pair : pairs) {
			elems = elems.insert(pair);
		}
	}
	
	/*@ assignable \nothing;
	    ensures \result.int_size() == 1 && \result.has(key, value);
	 */
	public static <KS, VS> BRelation<KS, VS> singleton(KS key, VS value) {
		return new BRelation<KS, VS>(JMLEqualsToEqualsRelation.singleton(key, value));
	}
	
	/*@ assignable \nothing;
        ensures \result.int_size() == 1 && \result.has(pair);
     */
	public static <KS, VS> BRelation<KS, VS> singleton(JMLEqualsEqualsPair<KS, VS> pair) {
		return BRelation.singleton(pair.key, pair.value);
	}
	
	/*@ assignable \nothing;
	    ensures \result <==> elems.isaFunction();
	 */
	public boolean isaFunction() {
		return elems.isaFunction();
	}

	/*@ assignable \nothing;
	    ensures (\forall V v; \result.has(v) <==> this.has(key, v));
	 */
	public BSet<V> elementImage(K key) {
		return new BSet<V>(elems.elementImage(key));
	}

	/*@ assignable \nothing;
        ensures (\forall K key; keys.has(key); 
          (\forall V v; \result.has(v) <==> this.has(key, v)));
     */
	public BSet<V> image(BSet<K> keys) {
		return new BSet<V>(elems.image(keys));
	}
	
	/* assignable \nothing;
	   ensures (\forall K key; (\forall V value; 
	     this.has(key, value) <==> \result.has(value, key)));
	 */
	public BRelation<V, K> inverse() {
		BRelation<V, K> res = new BRelation<V, K>();
		for (JMLEqualsEqualsPair<K, V> pair : elems) {
			res = res.add(pair.value, pair.key);
		}
		return res;
	}
	
	/* assignable \nothing;
	   ensures (\forall K key; \result.has(key) <==> this.has(key, value));
	 */
	public BSet<K> inverseElementImage(V value) {
		return new BSet<K>(elems.inverseElementImage(value));
	}

	/* assignable \nothing;
	   ensures (\forall V value; values.has(value);
	     (\forall K key; \result.has(key) <==> this.has(key, value)));
	 */
	public BSet<K> inverseImage(BSet<V> values) {
		return new BSet<K>(elems.inverseImage(values));
	}
	
	/*@ assignable \nothing;
	    ensures \result <==> (\exists V value; this.has(key, value));
	 */
	public boolean isDefinedAt(K key) {
		return elems.isDefinedAt(key);
	}
	
	/*@ assignable \nothing;
	    ensures (\forall K k; (\forall V v; \result.has(k, v) <==> this.has(k, v) ||
	       (k.equals(key) && v.equals(value))));
	 */
	public BRelation<K, V> add(K key, V value) {
		return new BRelation<K, V>(elems.add(key,  value));
	}
	
	/*@ also assignable \nothing;
	    ensures \result.equals(add(pair.key, pair.value));
	 */
	public BRelation<K, V> insert(JMLEqualsEqualsPair<K, V> pair) {
		return add(pair.key, pair.value);
	}
	
	/*@ also assignable \nothing;
	    ensures \result == elems.int_size();
	 */
	public int int_size() {
		return elems.int_size();
	}
	
	/*@ assignable \nothing;
	    ensures \result <==> elems.has(key, value);
	 */
	public boolean has(K key, V value) {
		return elems.has(key, value);
	}

	/*@ assignable \nothing;
        ensures \result <==> elems.has(pair);
 */
	public boolean has(JMLEqualsEqualsPair<K, V> pair) {
		return elems.has(pair);
	}
	
	/*@ also requires obj instanceof JMLEqualsEqualsPair;
	      assignable \nothing;
	      ensures \result <==> this.has((JMLEqualsEqualsPair) obj);
	    also requires !(obj instanceof JMLEqualsEqualsPair);
	      assignable \nothing;
	      ensures \result <==> false;
	 */
	public boolean has(Object obj) {
		if (obj instanceof JMLEqualsEqualsPair) {
			return has((JMLEqualsEqualsPair) obj);
		}
		return false;
	}

	/*@ also assignable \nothing;
	    ensures \result <==> elems.isEmpty();
	 */
	public boolean isEmpty() {
		return elems.isEmpty();
	}
	
	/** the inherited specification for clone should be correct */
	
	public Object clone() {
		return this;
	}
	
	/*@ also requires !(obj instanceof BSet);
	      assignable \nothing;
	      ensures \result <==> false;
	    also requires obj instanceof BSet;
	      assignable \nothing;
	      ensures \result <==> (\forall JMLEqualsEqualsPair<K, V> pair; 
	        this.has(pair) <==> ((BSet) obj).has(pair));  
	 */
	public boolean equals(Object obj) {
		if (obj instanceof ID) {
			return false;
		} else if (obj instanceof BRelation) {
			BRelation<K, V> rel = (BRelation<K, V>) obj;
			return elems.equals(rel.elems); 
		} else if (obj instanceof BSet) {
			try {
				BSet<JMLEqualsEqualsPair<K, V>> set = (BSet<JMLEqualsEqualsPair<K, V>>) obj;
				if (set.int_size() == int_size()) {
					for (JMLEqualsEqualsPair<K, V> pair : set) {
						if (!has(pair)) return false;
					}
					return true;
				}
			} catch (ClassCastException cse) {
				return false;
			}
		}
		return false;
	}
	
	/*@ also assignable \nothing;
	    ensures \result == elems.hashCode();
	 */
	public int hashCode() {
		return elems.hashCode();
	}
	
	/*@ assignable \nothing;
	    ensures (\forall K key; \result.has(key) <==> this.isDefinedAt(key));
	 */
	public BSet<K> domain() {
		return new BSet<K>(elems.domain());
	}
	
	/*@ assignable \nothing;
	    ensures (\forall V value; \result.has(value) <==> (\exists K key; this.has(key, value)));
	 */
	public BSet<V> range() {
		return new BSet<V>(elems.range());
	}
	
	/*@ assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<K, V> pair; 
	      \result.has(pair) <==> this.has(pair) && !pair.key.equals(key))
	      && \result.domain().equals(this.domain().difference(new BSet<K>(key)))
	      && (\forall V value; \result.range().has(value) <==>
	          (\exists K k; !k.equals(key); this.has(k, value)));
	 */
	public BRelation<K, V> removeFromDomain(K key) {
		return new BRelation<K, V>(elems.removeFromDomain(key));
	}
	
	/*@ assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<K, V> pair; 
	      \result.has(pair) <==> this.has(pair) && !pair.key.equals(key) && !pair.value.equals(value));
	 */
	public BRelation<K, V> remove(K key, V value) {
		return new BRelation<K, V>(elems.remove(key, value));		
	}
	
	/*@ also assignable \nothing;
	      ensures (\forall JMLEqualsEqualsPair<K, V> pair2; 
	      \result.has(pair2) <==> this.has(pair2) && !pair2.equals(pair));
 
	 */
	public BRelation<K, V> remove(JMLEqualsEqualsPair<K, V> pair) {
		return remove(pair.key, pair.value);
	}
	
	/*@ assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<D, V> rp; \result.has(rp) <==>
	      (\exists JMLEqualsEqualsPair<K, V> tp; this.has(tp);
	        (\exists JMLEqualsEqualsPair<D, K> op; otherRel.has(op);
	          op.value.equals(tp.key) && rp.value.equals(tp.value) && tp.key.equals(op.key))));
	 */
	public <D> BRelation<D, V> compose(BRelation<D, K> otherRel) {
		if (otherRel instanceof ID) {
			return (BRelation<D, V>) this;
		} else {
			BRelation<D, V> res = new BRelation<D, V>();
			for (JMLEqualsEqualsPair<D, K> pair : otherRel) {
				for (V val : elementImage(pair.value)) {
					res = res.add(pair.key, val);
				}
			}
			return res;
		}
	}
	
	/*@ assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<K, V> pair; \result.has(pair) <==>
	      this.has(pair) || otherRel.has(pair));
	 */
	public BRelation<K, V> union(JMLEqualsSet<JMLEqualsEqualsPair<K, V>> otherRel) {
		if (otherRel instanceof ID) {
			throw new UnsupportedOperationException("Error: cannot union with the identity relation.");
		}
		BRelation<K, V> res = this;
		for (JMLEqualsEqualsPair<K, V> pair : otherRel) {
			res = res.insert(pair);
		}
		return res;
	}
	
	/*@ assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<K, V> pair; \result.has(pair) <==>
          this.has(pair) && otherRel.has(pair));
     */
	public BRelation<K, V> intersection(JMLEqualsSet<JMLEqualsEqualsPair<K, V>> otherRel) {
		if (otherRel instanceof ID) {
			return ((ID) otherRel).intersection(this);
		}
		BRelation<K, V> res = new BRelation<K, V>();
		for (JMLEqualsEqualsPair<K, V> pair : otherRel) {
			if (this.has(pair)) {
				res = res.insert(pair);
			}
		}
		return res;
	}
	
	/*@ assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<K, V> pair; \result.has(pair) <==>
          this.has(pair) && !otherRel.has(pair));
     */
	public BRelation<K, V> difference(JMLEqualsSet<JMLEqualsEqualsPair<K, V>> otherRel) {
		if (otherRel instanceof ID) {
			BRelation<K, V> res = new BRelation<K, V>();
			for (JMLEqualsEqualsPair<K, V> pair : elems) {
				if (!pair.key.equals(pair.value)) {
					res = res.insert(pair);
				}
			}
			return res;
		} else {
			BRelation<K, V> res = this;
			for (JMLEqualsEqualsPair<K, V> pair : otherRel) {
				res = res.remove(pair);
			}
			return res;
		}
	}
	
	/*@ assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<K, V> pair; 
          \result.has(pair) <==> this.has(pair) && dom.has(pair.key))
       && \result.domain().equals(dom.intersection(this.domain()))
       && (\forall V value; \result.range().has(value) <==>
           (\exists K k; dom.has(k); this.has(k, value)));
    */
	public BRelation<K, V> restrictDomainTo(BSet<K> dom) {
		return new BRelation<K, V>(elems.restrictDomainTo(dom));
	}
	
	/*@ assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<K, V> pair; 
          \result.has(pair) <==> this.has(pair) && ran.has(pair.value))
       && \result.range().equals(ran.intersection(this.range()))
       && (\forall K k; \result.domain().has(k) <==>
         (\exists V v; ran.has(v); this.has(k, v)));
    */
	public BRelation<K, V> restrictRangeTo(BSet<V> ran) {
		return new BRelation<K, V>(elems.restrictRangeTo(ran));
	}
	
	/*@ also assignable \nothing;
	      ensures \result.equals(elems.toString());
	 */
	public String toString() {
		return elems.toString();
	}
	
	/*@ assignable \nothing;
        ensures \result.equals(elems.associations());
     */
	public /*@ non_null @*/
       JMLEqualsToEqualsRelationEnumerator<K, V> associations() {
		return elems.associations();
	}
	
	/*@ also assignable \nothing;
          ensures \result.equals(elems.iterator());
     */
    public JMLIterator<JMLEqualsEqualsPair<K, V>> iterator() {
    	return elems.iterator();
    }
    
    /*@ assignable \nothing;
        ensures (\forall JMLEqualsEqualsPair<K, V> pair;
          \result.has(pair) <==> this.has(pair));
     */
    public /*@ non_null @*/ BSet<JMLEqualsEqualsPair<K, V>> toSet() {
    	BSet<JMLEqualsEqualsPair<K, V>> res = new BSet<JMLEqualsEqualsPair<K, V>>();
    	for (JMLEqualsEqualsPair<K, V> pair: elems.toSet()) {
    		res = res.insert(pair);
    	}
    	return res;
    }

    /*@ also assignable \nothing;
          ensures (\forall JMLEqualsEqualsPair<K, V> pair;
            \result.count(pair) == 1 <==> this.has(pair));
 */
    public /*@ non_null @*/ JMLEqualsBag<JMLEqualsEqualsPair<K, V>> toBag() {
    	JMLEqualsBag<JMLEqualsEqualsPair<K, V>> res = new JMLEqualsBag<JMLEqualsEqualsPair<K, V>>();
    	for (JMLEqualsEqualsPair<K, V> pair: elems.toBag()) {
    		res = res.insert(pair);
    	}
    	return res;
    }
    
    /*@ also assignable \nothing;
          ensures (\forall JMLEqualsEqualsPair<K, V> pair;
            \result.has(pair) <==> this.has(pair));
     */
    public /*@ non_null @*/ JMLEqualsSequence<JMLEqualsEqualsPair<K, V>> toSequence() {
    	JMLEqualsSequence<JMLEqualsEqualsPair<K, V>> res = new JMLEqualsSequence<JMLEqualsEqualsPair<K, V>>();
    	for (JMLEqualsEqualsPair<K, V> pair: elems.toSequence()) {
    		res = res.insertBack(pair);
    	}
    	return res;
    }
    
    /*@ assignable \nothing;
        ensures (\forall JMLEqualsValuePair<K, JMLEqualsSet<V>> pair; \result.has(pair); 
           this.isDefinedAt(pair.key) && pair.value.equals(this.elementImage(pair.key)));
      */
    public /*@ non_null @*/ JMLValueSet<JMLEqualsValuePair<K, JMLEqualsSet<V>>> imagePairSet() {
    	return elems.imagePairSet();
    }
    
    /*@ assignable \nothing;
        ensures \result.equals(elems.imagePairs());
     */
    public /*@ non_null @*/
    JMLEqualsToEqualsRelationImageEnumerator<K, V> imagePairs() {
    	return elems.imagePairs();
    }
    
    /*@ assignable \nothing;
        ensures \result.equals(elems.domainElements());
     */
    public /*@ non_null @*/ JMLEqualsSetEnumerator<K> domainElements()
    {
    	return elems.domainElements();
    }
    
    /*@ assignable \nothing;
        ensures \result.equals(elems.rangeElements());
     */
    public /*@ non_null @*/ JMLEqualsSetEnumerator<V> rangeElements()
    {
    	return elems.rangeElements();
    }
    
    /*@ assignable \nothing;
        ensures \result.equals(elems.toFunction());
     */
    public JMLEqualsToEqualsMap<K, V> toFunction() {
    	return elems.toFunction();
    }
    
    // domain restriction == restrictDomainTo
    // range restriction == restrictRangeTo
    
    /*@ assignable \nothing;
        ensures \result.equals(this.restrictDomainTo(this.domain().difference(domain)));
     */
    public BRelation<K, V> domainSubtraction(BSet<K> domain) {
    	return restrictDomainTo(domain().difference(domain));
    }
    
    /*@ assignable \nothing;
        ensures \result.equals(restrictRangeTo(range().difference(range)));
     */
    public BRelation<K, V> rangeSubtraction(BSet<V> range) {
    	return restrictRangeTo(range().difference(range));
    }
    
    /*@ assignable \nothing;
        ensures \result.equals(otherRel.compose(this));
     */
	public <D> BRelation<K, D> backwardCompose(BRelation<V, D> otherRel) {
		return otherRel.compose(this);
	}

	/*@ assignable \nothing;
	    ensures \result.equals(other.union(domainSubtraction(other.domain())));
	 */
	public BRelation<K, V> override(BRelation<K, V> other) {
		return other.union(domainSubtraction(other.domain()));
	}
	
	/*@ assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<K, JMLEqualsEqualsPair<V, D>> pair; \result.has(pair) <==>
	       (\exists JMLEqualsEqualsPair<K, V> tp; this.has(tp);
	         (\exists JMLEqualsEqualsPair<K, D> op; other.has(op);
	           tp.key.equals(op.key) && tp.key.equals(pair.key) && 
	             pair.value.equals(new JMLEqualsEqualsPair<V, D>(tp.value, op.value)))));
	 */
	public <D> BRelation<K, JMLEqualsEqualsPair<V, D>> parallel(BRelation<K, D> other) {
		BRelation<K, JMLEqualsEqualsPair<V, D>> res = new BRelation<K, JMLEqualsEqualsPair<V, D>>();
		for (JMLEqualsEqualsPair<K, V> pair : elems) {
			for (D val : other.elementImage(pair.key)) {
				res = res.add(pair.key, new JMLEqualsEqualsPair<V, D>(pair.value, val));
			}
		}
		return res;
	}
	
	/*@ assignable \nothing;
	    ensures (\forall JMLEqualsEqualsPair<JMLEqualsEqualsPair<K, K1>, JMLEqualsEqualsPair<V, V1>> pair;
	      \result.has(pair) <==> this.has(pair.key) && other.has(pair.value));
	 */
	public <K1, V1> BRelation<JMLEqualsEqualsPair<K, K1>, JMLEqualsEqualsPair<V, V1>> directProd(BRelation<K1, V1> other) {
		BRelation<JMLEqualsEqualsPair<K, K1>, JMLEqualsEqualsPair<V, V1>> res = new BRelation<JMLEqualsEqualsPair<K, K1>, JMLEqualsEqualsPair<V, V1>>();
		for (JMLEqualsEqualsPair<K, V> pair : elems) {
			for (JMLEqualsEqualsPair<K1, V1> pair2 : other.elems) {
				res = res.add(new JMLEqualsEqualsPair<K, K1>(pair.key, pair2.key),
						      new JMLEqualsEqualsPair<V, V1>(pair.value, pair2.value));
			}
		}
		return res;
	}
    
	/*@ assignable \nothing;
	    ensures \result <==> dom.equals(domain()) && range().isSubset(ran);
	 */
    public boolean isTotal(BSet<K> dom, BSet<V> ran) {
    	return dom.equals(domain()) && range().isSubset(ran);
    }
    
	/*@ assignable \nothing;
        ensures \result <==> domain().isSubset(dom) && ran.equals(range());
    */
    public boolean isSurjective(BSet<K> dom, BSet<V> ran) {
    	return domain().isSubset(dom) && ran.equals(range());
    }	
    
	/*@ assignable \nothing;
        ensures \result <==> isTotal(dom, ran) && isSurjective(dom, ran);
     */
    public boolean isTotalSurjective(BSet<K> dom, BSet<V> ran) {
    	return isTotal(dom, ran) && isSurjective(dom, ran);
    }
	
	/*@ assignable \nothing;
        ensures \result <==> isaFunction() && isRelation(dom, ran);
     */
	public boolean isFunction(BSet<K> dom, BSet<V> ran) {
		return isaFunction() && isRelation(dom, ran);
	}
	
	/*@ assignable \nothing;
        ensures \result <==> domain().isSubset(dom) && range().isSubset(ran);
     */
	public boolean isRelation(BSet<K> dom, BSet<V> ran) {
		return domain().isSubset(dom) && range().isSubset(ran);
	}

	/*@ assignable \nothing;
        ensures \result <==> isaFunction() && isTotal(dom, ran) && range().isSubset(ran);
     */
	public boolean isTotalFunction(BSet<K> dom, BSet<V> ran) {
		return isaFunction() && isTotal(dom, ran) && range().isSubset(ran);
	}
	
	/*@ assignable \nothing;
        ensures \result <==> isaFunction() && inverse().isaFunction() && isRelation(dom, ran);
     */
	public boolean isPartialInjection(BSet<K> dom, BSet<V> ran) {
		return isaFunction() && inverse().isaFunction() && isRelation(dom, ran);
	}
	
	/*@ assignable \nothing;
        ensures \result <==> isPartialInjection(dom, ran) && isTotal(dom, ran);
     */
	public boolean isTotalInjection(BSet<K> dom, BSet<V> ran) {
		return isPartialInjection(dom, ran) && isTotal(dom, ran);
	}
	
	/*@ assignable \nothing;
        ensures \result <==> isaFunction() && isSurjective(dom, ran);
     */
	public boolean isPartialSurjection(BSet<K> dom, BSet<V> ran) {
		return isaFunction() && isSurjective(dom, ran);
	}

	/*@ assignable \nothing;
        ensures \result <==> isTotalFunction(dom, ran) && isPartialSurjection(dom, ran);
     */
	public boolean isTotalSurjection(BSet<K> dom, BSet<V> ran) {
		return isTotalFunction(dom, ran) && isPartialSurjection(dom, ran);
	}
	
	/*@ assignable \nothing;
        ensures \result <==> isPartialInjection(dom, ran) && isPartialSurjection(dom, ran);
     */
	public boolean isInjection(BSet<K> dom, BSet<V> ran) {
		return isPartialInjection(dom, ran) && isPartialSurjection(dom, ran);
	}
	
	/*@ public normal_behavior
	      requires this.isaFunction();
	      assignable \nothing;
	      ensures \result.equals(this.elementImage(key).choose());
	    also public exceptional_behavior
	      requires !this.isaFunction();
	      assignable \nothing;
	      signals (IllegalStateException);
	 */
	public V apply(K key) {
		if (!isaFunction()) {
			throw new IllegalStateException("Error: only functions can be applied.");
		} else {
			return elementImage(key).choose();
		}
	}
	
	/*@ also assignable \nothing;
	    ensures (\forall BSet<JMLEqualsEqualsPair<K, V>> s; \result.has(s) <==> s.isSubset(this));
	 */
	public BSet<BSet<JMLEqualsEqualsPair<K, V>>> pow() {
		return toSet().pow();
	}
		
	/*@ also assignable \nothing;
        ensures (\forall BSet<JMLEqualsEqualsPair<K, V>> s; \result.has(s) <==> s.isSubset(this) && !s.isEmpty());
     */
	public BSet<BSet<JMLEqualsEqualsPair<K, V>>> pow1() {
		return toSet().pow1();
	}

    /*@ assignable \nothing;
        ensures \result <==> (\forall JMLEqualsEqualsPair<K, V> e; col.contains(e); this.has(e));
     */
	public boolean containsAll(java.util.Collection<JMLEqualsEqualsPair<K, V>> col) {
		for (JMLEqualsEqualsPair<K, V> pair : col) {
			if (!has(pair)) return false;
		}
		return true;
	}
	
    /*@ assignable \nothing;
        ensures \result <==> (\forall JMLEqualsEqualsPair<K, V> e; this.has(e); other.has(e));
     */
	public boolean isSubset(JMLEqualsSet<JMLEqualsEqualsPair<K, V>> other) {
		for (JMLEqualsEqualsPair<K, V> pair : this) {
			if (!other.has(pair)) return false;
		}
		return true;
	}
	
	/*@ assignable \nothing;
        ensures \result <==> this.isSubset(other) && !this.equals(other);
	 */
	public boolean isProperSubset(JMLEqualsSet<JMLEqualsEqualsPair<K, V>> other) {
		return this.isSubset(other) && !this.equals(other);
	}
	
    /** inherited specification is correct */
	
	public JMLEqualsEqualsPair<K, V> choose() {
		return elems.iterator().next();
	}

	/*@ assignable \nothing;
	    ensures \result <==> true;
	 */
	public boolean finite() {
		return true;
	}
}
