// @(#)$Id: JMLMap.java-generic,v 1.35 2008/10/08 16:17:08 leavens Exp $

// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.


package org.jmlspecs.models;

import java.util.Enumeration;

/** Maps (i.e., binary relations that are functional) from non-null
 *  elements of {@link K} to non-null elements of {@link
 *  V}.  The first type, <kbd>K</kbd>, is called
 *  the domain type of the map; the second type,
 *  <kbd>V</kbd>, is called the range type of the map.  A
 *  map can be seen as a set of pairs, of form <em>(dv, rv)</em>,
 *  consisting of an element of the domain type, <em>dv</em>, and an
 *  element of the range type, <em>rv</em>.  Alternatively, it can be
 *  seen as a partial function that maps each element of the domain to
 *  an element of the range type.
 *
 *  <p> This type is a subtype of {@link
 *  JMLObjectToObjectRelation}, and as such as can be treated as a
 *  binary relation or a set valued function also.  See the
 *  documentation for {@link JMLObjectToObjectRelation} and for the
 *  methods inherited from this supertype for more information.
 *
 *  <p> This type considers elements <kbd>val</kbd> and <kbd>dv</kbd>
 *  of the domain type, to be distinct just when
 *  <kbd>val != dv</kbd>.  It considers elements of
 *  <kbd>r</kbd> and <kbd>rv</kbd> of the range type to be distinct
 *  just when <kbd>r != rv</kbd>.  Cloning takes place for
 *  the domain or range elements if the corresponding domain or range
 *  type is {@link JMLType}.
 *
 * @version $Revision: 1.35 $
 * @author Gary T. Leavens
 * @author Clyde Ruby
 * @see JMLCollection
 * @see JMLType
 * @see JMLObjectToObjectRelation
 * @see JMLObjectToObjectRelationEnumerator
 * @see JMLObjectToObjectRelationImageEnumerator
 * @see JMLValueSet
 * @see JMLObjectSet
 * @see JMLObjectToObjectMap
 * @see JMLValueToObjectMap
 * @see JMLObjectToValueMap
 * @see JMLValueToValueMap
 * @see JMLObjectToObjectRelation#toFunction()
 */
//-@ immutable
public /*@ pure @*/
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
class JMLObjectToObjectMap<K, V> extends JMLObjectToObjectRelation<K, V> {

    /*@ public invariant isaFunction();
      @ public invariant_redundantly
      @        (\forall K dv; isDefinedAt(dv);
      @                                  elementImage(dv).int_size() == 1);
      @*/

    /** Initialize this map to be the empty mapping.
     * @see #EMPTY
     */
    /*@  public normal_behavior
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures theRelation.equals(new JMLValueSet<JMLObjectValuePair<K, JMLObjectSet<V>>>());
      @    ensures_redundantly theRelation.isEmpty();
      @*/
    public JMLObjectToObjectMap() 
    {
        super();
    }

    /** Initialize this map to be a mapping that maps the given domain
     * element to the given range element.
     * @see #singletonMap(K, V)
     * @see #JMLObjectToObjectMap(JMLObjectObjectPair)
     */
    /*@  public normal_behavior
      @    requires dv != null && rv != null;
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures (theRelation.int_size() == 1) && elementImage(dv).has(rv);
      @    ensures_redundantly isDefinedAt(dv);
      @*/
    public JMLObjectToObjectMap(/*@ non_null @*/ K dv,
                                   /*@ non_null @*/ V rv)
    {
        super(dv, rv);
    }

    /** Initialize this map to be a mapping that maps the key in the
     * given pair to the value in that pair.
     * @see #singletonMap(JMLObjectObjectPair)
     * @see #JMLObjectToObjectMap(K, V)
     */
    /*@  public normal_behavior
      @    requires pair != null;
      @    assignable theRelation, owner, elementType, containsNull;
      @    ensures (theRelation.int_size() == 1)
      @         && elementImage(pair.key).has(pair.value);
      @    ensures_redundantly isDefinedAt(pair.key);
      @*/
    public JMLObjectToObjectMap(/*@ non_null @*/
                                   JMLObjectObjectPair<K, V> pair)
    {
        super(pair.key, pair.value);
    }

    /** Initialize this map based on the representation values given.
     */
    //@    requires ipset != null && dom != null && 0 <= sz;
    //@    assignable theRelation, owner, elementType, containsNull;
    //@    ensures imagePairSet_ == ipset && domain_ == dom && size_ == sz;
    protected JMLObjectToObjectMap(JMLValueSet<JMLObjectValuePair<K, JMLObjectSet<V>>> ipset,
                                      JMLObjectSet<K> dom,
                                      int sz)
    {
        super(ipset, dom, sz);
    }

    /** The empty JMLObjectToObjectMap.
     * @see #JMLObjectToObjectMap()
     */
    public static final /*@ non_null @*/ JMLObjectToObjectMap EMPTY
        = new JMLObjectToObjectMap();

    /** Return the singleton map containing the given association.
     * @see #JMLObjectToObjectMap(K, V)
     * @see #singletonMap(JMLObjectObjectPair)
     */
    /*@ public normal_behavior
      @    requires dv != null && rv != null;
      @    ensures \result != null
      @         && \result.equals(new JMLObjectToObjectMap<K, V>(dv, rv));
      @*/
    public static <SK, SR extends JMLType> /*@ pure @*/ /*@ non_null @*/
        JMLObjectToObjectMap<SK, SR>
        singletonMap(/*@ non_null @*/ SK dv,
                     /*@ non_null @*/ SR rv)
    {
        return new JMLObjectToObjectMap<SK, SR>(dv, rv);
    }

    /** Return the singleton map containing the association described
     * by the given pair.
     * @see #JMLObjectToObjectMap(JMLObjectObjectPair)
     * @see #singletonMap(K, V)
     */
    /*@ public normal_behavior
      @    requires pair != null;
      @    ensures \result != null
      @         && \result.equals(new JMLObjectToObjectMap(pair));
      @*/
    public static <SK, SR extends JMLType> /*@ pure @*/ /*@ non_null @*/
        JMLObjectToObjectMap<SK, SR>
        singletonMap(/*@ non_null @*/ JMLObjectObjectPair<SK, SR> pair)
    {
        return new JMLObjectToObjectMap<SK, SR>(pair);
    }

    /** Tells whether this relation is a function.
     */
    /*@ also
      @    public normal_behavior
      @      ensures \result;
      @*/
    //@ pure
    public boolean isaFunction()
    {
        return true;
    }

    /** Return the range element corresponding to dv, if there is one.
     *
     * @param dv the domain element for which an association is
     * sought (the key to the table).
     * @exception JMLNoSuchElementException when dv is not associated
     * to any range element by this.
     * @see JMLObjectToObjectRelation#isDefinedAt
     * @see JMLObjectToObjectRelation#elementImage
     * @see JMLObjectToObjectRelation#image
     */
    /*@  public normal_behavior
      @    requires isDefinedAt(dv);
      @    ensures elementImage(dv).has(\result);
      @ also
      @  public exceptional_behavior
      @    requires !isDefinedAt(dv);
      @    signals_only JMLNoSuchElementException;
      @*/
    public /*@ non_null @*/ V apply(K dv)
        throws JMLNoSuchElementException
    {
        JMLObjectSet<V> img = elementImage(dv);
        if (img.int_size() == 1) {
            V res = img.choose();
            //@ assume res != null;
            return res;
        } else {
            throw new JMLNoSuchElementException("Map not defined at " + dv);
        }
    } //@ nowarn NonNullResult;

    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof JMLObjectToObjectMap<K, V>
      @          && ((JMLObjectToObjectMap<K, V>)\result)
      @                .theRelation.equals(this.theRelation);
      @*/
    //@ pure
    public /*@ non_null @*/ Object clone() 
    {
        return new JMLObjectToObjectMap<K, V>(imagePairSet_, domain_, size_);
    } //@ nowarn Post;

    /** Return a new map that is like this but maps the given domain
     *  element to the given range element.  Any previously existing
     *  mapping for the domain element is removed first.
     * @see JMLObjectToObjectRelation#insert(K, V)
     */
    /*@  public normal_behavior
      @    requires dv != null && rv != null;
      @    requires !isDefinedAt(dv) ==> int_size() < Integer.MAX_VALUE;
      @    ensures \result.equals(this.removeDomainElement(dv).add(dv, rv));
      @*/
    public /*@ non_null @*/
        JMLObjectToObjectMap<K, V> extend(/*@ non_null @*/ K dv,
                                       /*@ non_null @*/ V rv) 
    {
        JMLObjectToObjectMap<K, V> newMap = this.removeDomainElement(dv);
        newMap = newMap.disjointUnion(new JMLObjectToObjectMap<K, V>(dv, rv));
        return newMap;
    } //@ nowarn Exception;

    /** Return a new map that is like this but has no association for the
     *  given domain element.
     * @see JMLObjectToObjectRelation#removeFromDomain
     */
    /*@  public normal_behavior
      @    ensures \result.equals(removeFromDomain(dv).toFunction());
      @    ensures_redundantly !isDefinedAt(dv) ==> \result.equals(this);
      @*/
    public /*@ non_null @*/
        JMLObjectToObjectMap<K, V> removeDomainElement(K dv)
    {
        return super.removeFromDomain(dv).toFunction();
    }

    /** Return a new map that is the composition of this and the given
     *  map.  The composition is done in the usual order; that is, if
     *  the given map maps x to y and this maps y to z, then the
     *  result maps x to z.
     * @see #compose(JMLObjectToObjectMap)
     */
    /*@  public normal_behavior
      @    requires othMap != null;
      @    ensures (\forall JMLValueObjectPair<D, V> pair; ;
      @                 \result.theRelation.has(pair) 
      @                    == (\exists K val;
      @                            othMap.elementImage(pair.key).has(val);
      @                            this.elementImage(val).has(pair.value) 
      @                            )
      @                );
      @*/
    public /*@ non_null @*/ <D extends JMLType>
        JMLValueToObjectMap<D, V>
        compose(/*@ non_null @*/ JMLValueToObjectMap<D, K> othMap)
    {
        return super.compose(othMap).toFunction();
    }

    /** Return a new map that is the composition of this and the given
     *  map.  The composition is done in the usual order; that is, if
     *  the given map maps x to y and this maps y to z, then the
     *  result maps x to z.
     * @see #compose(JMLValueToObjectMap)
     */
    /*@  public normal_behavior
      @    requires othMap != null;
      @    ensures (\forall JMLObjectObjectPair<D, V> pair; ;
      @                 \result.theRelation.has(pair) 
      @                    == (\exists K val;
      @                            othMap.elementImage(pair.key).has(val);
      @                            this.elementImage(val).has(pair.value) 
      @                            )
      @                );
      @*/
    public /*@ non_null @*/ <D>
        JMLObjectToObjectMap<D, V>
        compose(/*@ non_null @*/ JMLObjectToObjectMap<D, K> othMap)
    {
        return super.compose(othMap).toFunction();
    }

    /** Return a new map that only maps elements in the given domain
     * to the corresponding range elements in this map.
     * @see #rangeRestrictedTo
     * @see JMLObjectToObjectRelation#restrictDomainTo
     */
    /*@  public normal_behavior
      @    requires dom != null;
      @    ensures (\forall JMLObjectObjectPair<K, V> pair; ; 
      @                 \result.theRelation.has(pair)
      @                    == 
      @                       dom.has(pair.key) 
      @                    && elementImage(pair.key).has(pair.value)
      @                );
      @*/
    public /*@ non_null @*/ 
        JMLObjectToObjectMap<K, V> 
        restrictedTo(/*@ non_null @*/ JMLObjectSet<K> dom) 
    {
        return super.restrictDomainTo(dom).toFunction();
    }

    /** Return a new map that is like this map but only contains
     *  associations that map to range elements in the given set.
     * @see #restrictedTo
     * @see JMLObjectToObjectRelation#restrictRangeTo
     */
    /*@  public normal_behavior
      @    requires rng != null;
      @    ensures (\forall JMLObjectObjectPair<K, V> pair; ;
      @                 \result.theRelation.has(pair)
      @                    == 
      @                       rng.has(pair.value) 
      @                    && elementImage(pair.key).has(pair.value)
      @                );
      @*/
    public /*@ non_null @*/ 
        JMLObjectToObjectMap<K, V>
        rangeRestrictedTo(/*@ non_null @*/ JMLObjectSet<V> rng)
    {
        return super.restrictRangeTo(rng).toFunction();
    }

    /** Return a new map that is like the union of the given map and
     *  this map, except that if both define a mapping for a given domain
     *  element, then only the mapping in the given map is retained.
     * @see #clashReplaceUnion
     * @see #disjointUnion
     * @see JMLObjectToObjectRelation#union
     */
    /*@  public normal_behavior
      @    requires othMap != null;
      @    requires int_size()
      @             <= Integer.MAX_VALUE - othMap.difference(this).int_size();
      @    ensures (\forall JMLObjectObjectPair<K, V> pair; ;
      @                 \result.theRelation.has(pair)
      @                    == 
      @                       othMap.elementImage(pair.key).has(pair.value)
      @                    || (!othMap.isDefinedAt(pair.key)
      @                        && this.elementImage(pair.key).has(pair.value))
      @                );
      @*/
    public /*@ non_null @*/ 
        JMLObjectToObjectMap<K, V>
        extendUnion(/*@ non_null @*/ JMLObjectToObjectMap<K, V> othMap) 
        throws IllegalStateException
    {
        JMLObjectToObjectMap<K, V> newMap 
            = this.restrictedTo(this.domain_.difference(othMap.domain_));
        if (newMap.size_ <= Integer.MAX_VALUE - othMap.size_) {
            return
                new JMLObjectToObjectMap<K, V>(newMap.imagePairSet_
                                            .union(othMap.imagePairSet_),
                                            newMap.domain_
                                            .union(othMap.domain_),
                                            newMap.size_ + othMap.size_);
        } else {
            throw new IllegalStateException(TOO_BIG_TO_UNION);
        }
    }

    /** Return a new map that is like the union of the given map and
     * this map, except that if both define a mapping for a given
     * domain element, then each of these clashes is replaced by a
     * mapping from the domain element in question to the given range
     * element.
     * @param othMap the other map.
     * @param errval the range element to use when clashes occur.
     * @see #extendUnion
     * @see #disjointUnion
     * @see JMLObjectToObjectRelation#union
     */
    /*@  public normal_behavior
      @    requires othMap != null && errval != null;
      @    requires int_size()
      @             <= Integer.MAX_VALUE - othMap.difference(this).int_size();
      @    ensures (\forall JMLObjectObjectPair<K, V> pair; ; 
      @                 \result.theRelation.has(pair)
      @                    == 
      @                       (!othMap.isDefinedAt(pair.key)
      @                        && this.elementImage(pair.key).has(pair.value))
      @                    || (!this.isDefinedAt(pair.key)
      @                        && othMap.elementImage(pair.key)
      @                                 .has(pair.value))
      @                    || (this.isDefinedAt(pair.key)
      @                        && othMap.isDefinedAt(pair.key)
      @                        && pair.value _rangeEquals_ (errval))
      @                );
      @ implies_that
      @    requires othMap != null && errval != null;
      @*/
    public /*@ non_null @*/ 
        JMLObjectToObjectMap<K, V>
        clashReplaceUnion(JMLObjectToObjectMap<K, V> othMap,
                          V errval)
        throws IllegalStateException
    {
        JMLObjectSet<K> overlap = this.domain_.intersection(othMap.domain_);
        Enumeration<K> overlapEnum = overlap.elements();
        othMap = othMap.restrictedTo(othMap.domain_.difference(overlap));
        JMLObjectToObjectMap<K, V> newMap
            = this.restrictedTo(this.domain_.difference(overlap));
        JMLObjectToObjectRelation<K, V> newRel;
        if (newMap.size_ <= Integer.MAX_VALUE - othMap.size_) {
            newRel = new JMLObjectToObjectRelation<K, V>(newMap.imagePairSet_
                                                      .union(othMap
                                                             .imagePairSet_),
                                                      newMap.domain_
                                                      .union(othMap.domain_),
                                                      newMap.size_
                                                      + othMap.size_);
        } else {
                throw new IllegalStateException(TOO_BIG_TO_UNION);
        }
        K dv;
        while (overlapEnum.hasMoreElements()) {
            //@ assume overlapEnum.moreElements;
            dv = overlapEnum.nextElement();
            //@ assume dv != null
            newRel = newRel.add(dv, errval);
        }
        return newRel.toFunction();
    } //@ nowarn Exception;

    /** Return a map that is the disjoint union of this and othMap.
     *  @param othMap the other mapping
     *  @exception JMLMapException the ranges of this and othMap have elements
     *  in common (i.e., when they interesect).
     * @see #extendUnion
     * @see #clashReplaceUnion
     * @see JMLObjectToObjectRelation#union
     */
    /*@  public normal_behavior
      @    requires othMap != null
      @          && this.domain().intersection(othMap.domain()).isEmpty();
      @    requires int_size() <= Integer.MAX_VALUE - othMap.int_size();
      @    ensures \result.equals(this.union(othMap));
      @ also
      @  public exceptional_behavior
      @    requires othMap != null
      @          && !this.domain().intersection(othMap.domain()).isEmpty();
      @    signals_only JMLMapException;
      @*/
    public /*@ non_null @*/ 
        JMLObjectToObjectMap<K, V> 
        disjointUnion(/*@ non_null @*/ JMLObjectToObjectMap<K, V> othMap) 
        throws JMLMapException, IllegalStateException
    {
        JMLObjectSet<K> overlappingDom = domain_.intersection(othMap.domain_);
        if (overlappingDom.isEmpty()) {
            if (this.size_ <= Integer.MAX_VALUE - othMap.size_) {
                return new JMLObjectToObjectMap<K, V>(this.imagePairSet_
                                                   .union(othMap
                                                          .imagePairSet_),
                                                   this.domain_
                                                   .union(othMap.domain_),
                                                   this.size_ + othMap.size_);
            } else {
                throw new IllegalStateException(TOO_BIG_TO_UNION);
            }
        } else {
            throw new JMLMapException("Overlapping domains in "
                                      + " disjointUnion operation",
                                      overlappingDom);
        }
    }
    
}