// @(#)$Id: JMLSet.java-generic,v 1.83 2006/12/24 22:35:54 leavens Exp $

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

/** Sets of objects.  This type uses "==" to
 * compare elements, and does not clone elements that are passed into and
 * returned from the set's methods.
 *
 * <p>
 * For the purposes of informal specification in the methods below, we
 * assume there is a model field
 * <pre>public model mathematical_set theSet;</pre>
 * that you can think of as a mathematical set of objects.
 *
 * @version $Revision: 1.83 $
 * @author Gary T. Leavens, with help from Albert Baker, Clyde Ruby,
 * and others.
 * @see JMLCollection
 * @see JMLType
 * @see JMLEqualsSet
 * @see JMLValueSet
 * @see JMLObjectSetEnumerator
 * 
 * @see JMLObjectBag
 * @see JMLEqualsBag
 * @see JMLValueBag
 */
//-@ immutable
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public /*@ pure @*/ class JMLObjectSet<E>
    implements JMLCollection<E>
{

    //*********************** equational theory ***********************

    /*@ public invariant (\forall JMLObjectSet<E> s2; s2 != null;
      @                    (\forall E e1, e2; ;
      @                          equational_theory(this, s2, e1, e2) ));
      @*/

    /** An equational specification of the properties of sets.
     */
    /*@ public normal_behavior
      @ {|
      @     // The following are defined by using has and induction.
      @
      @       ensures \result <==> !(new JMLObjectSet<E>()).has(e1);
      @     also
      @       ensures \result <==>
      @           s.insert(null).has(e2) == (e2 == null || s.has(e2));
      @     also
      @       ensures \result <==>
      @         (e1 != null
      @          ==> s.insert(e1).has(e2)
      @                == (e1 == e2 || s.has(e2)));
      @     also
      @       ensures \result <==>
      @           (new JMLObjectSet()).int_size() == 0;
      @     also
      @       ensures \result <==>
      @           s.insert(e1).int_size()
      @              == (s.has(e1) ? s.int_size() : s.int_size() + 1);
      @     also
      @       ensures \result <==>
      @           s.isSubset(s2)
      @              == (\forall Object o; ; s.has(o) ==> s2.has(o));
      @     also
      @       ensures \result <==>
      @           s.equals(s2) == (s.isSubset(s2) && s2.isSubset(s));
      @     also
      @       ensures \result <==>
      @           (new JMLObjectSet<E>()).remove(e1).equals(new JMLObjectSet<E>());
      @     also
      @       ensures \result <==>
      @           s.insert(null).remove(e2)
      @                     .equals
      @                     (e2 == null ? s : s.remove(e2).insert(null));
      @     also
      @       ensures \result <==>
      @           e1 != null
      @            ==> s.insert(e1).remove(e2)
      @                     .equals
      @                     (e1 == e2
      @                        ? s : s.remove(e2).insert(e1));
      @     also
      @       ensures \result <==>
      @         (s.union(s2)).has(e1) == (s.has(e1) || s2.has(e1));
      @     also
      @       ensures \result <==>
      @         (s.intersection(s2)).has(e1) == (s.has(e1) && s2.has(e1));
      @     also
      @       ensures \result <==>
      @         (s.difference(s2)).has(e1) == (s.has(e1) && !s2.has(e1));
      @
      @
      @     // The following are all defined as abbreviations.
      @
      @    also
      @      ensures \result <==>
      @         s.isEmpty() == (s.int_size() == 0);
      @    also
      @      ensures \result <==>
      @         (new JMLObjectSet<E>(e1)).equals(new JMLObjectSet<E>().insert(e1));
      @    also
      @      ensures \result <==>
      @         s.isProperSubset(s2)
      @               == ( s.isSubset(s2) && !s.equals(s2));
      @    also
      @      ensures \result <==>
      @         s.isSuperset(s2) == s2.isSubset(s);
      @    also
      @      ensures \result <==>
      @         s.isProperSuperset(s2) == s2.isProperSubset(s);
      @ |}
      @
      @ implies_that    // other ways to specify some operations
      @
      @      ensures \result <==> (new JMLObjectSet<E>()).isEmpty();
      @ 
      @      ensures \result <==> !s.insert(e1).isEmpty();
      @
      @      ensures \result <==>
      @         (new JMLObjectSet<E>(null)).has(e2) == (e2 == null);
      @
      @      ensures \result <==>
      @         (e1 != null
      @          ==> new JMLObjectSet<E>(e1).has(e2)
      @              == (e1 == e2));
      @
      static public pure model boolean equational_theory(JMLObjectSet<E> s,
                                                  JMLObjectSet<E> s2,
                                                  E e1,
                                                  E e2);
      @*/
 
    //@ public  invariant elementType <: \type(E);
    /*@ public invariant
      @           (\forall Object o; o != null && has(o);
      @                                 \typeof(o) <: elementType);
      @*/

    //@ public invariant containsNull <==> has(null);
    //@ public invariant_redundantly isEmpty() ==> !containsNull;

    /** The list representing the elements of this set.
     */
    protected final /*@ nullable @*/ JMLListObjectNode<E> the_list;
    //@                                      in objectState;
    //@                  maps the_list.elementState \into elementState;

    /** The number of elements in this set.
     */
    /*@ spec_public @*/ protected final int size;
    //@                                      in objectState;

    //@ protected invariant the_list == null ==> size == 0;
    //@ protected invariant the_list != null ==> size == the_list.int_size();
    //@ protected invariant (the_list == null) == (size == 0);
    //@ protected invariant size >= 0;
    /*@ protected invariant the_list != null && the_list.next != null ==>
      @       !the_list.next.has(the_list.val);
      @*/
    //@ protected invariant_redundantly (* the_list has no duplicates *);

    //@ protected invariant size == 0 ==> !containsNull;

    //@ public invariant owner == null;

    //************************* Constructors ********************************

    /** Initialize this to be an empty set.
     * @see #EMPTY
     */
    /*@ public normal_behavior
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures this.isEmpty();
      @    ensures_redundantly (* this is an empty set *);
      @ implies_that
      @    ensures elementType <: \type(E) && !containsNull;
      @*/
    public JMLObjectSet() {
        //@ set owner = null;
        the_list = null;
        size = 0;
        //@ set elementType = \type(E);
        //@ set containsNull = false;
    }  

    /** Initialize this to be a singleton set containing the given element.
     * @see #singleton
     */
    public JMLObjectSet (E e)
        /*@ public normal_behavior
          @    assignable objectState, elementType, containsNull, owner;
          @    ensures this.has(e) && this.int_size() == 1;
          @    ensures_redundantly
          @      (* this is a singleton set containing e *); 
          @*/
    {
        //@ set owner = null;
        the_list = JMLListObjectNode.cons(e, null);  // cons() clones if needed
        size = 1;
        //@ set elementType = (e == null ? \type(Object) : \typeof(e));
        //@ set containsNull = (e == null);
    }  

    /** Initialize this set with the given instance variables.
     */
    //@    requires (ls == null) == (sz == 0);
    //@    requires sz >= 0;
    //@    assignable objectState, elementType, containsNull, owner;
    //@    ensures ls != null ==> elementType == ls.elementType;
    //@    ensures ls != null ==> containsNull == ls.containsNull;
    //@    ensures ls == null ==> elementType <: \type(E);
    //@    ensures ls == null ==> !containsNull;
    protected JMLObjectSet (/*@ nullable @*/ JMLListObjectNode<E> ls, int sz) {
        //@ set owner = null;
        the_list = ls;
        size = sz;
        /*@ set elementType = ((ls == null) ? \type(E)
          @                                 : ls.elementType);
          @*/
        //@ set containsNull = ((ls == null) ? false : ls.containsNull);
    }

    /** Initialize this set with the given list.
     */
    //@    assignable objectState, elementType, containsNull, owner;
    //@    ensures ls != null ==> elementType == ls.elementType;
    //@    ensures ls != null ==> containsNull == ls.containsNull;
    //@    ensures ls == null ==> elementType <: \type(E);
    //@    ensures ls == null ==> !containsNull;
    protected JMLObjectSet (/*@ nullable @*/ JMLListObjectNode<E> ls) {
        this(ls, (ls == null) ? 0 : ls.int_size()); 
    }

    //**************************** Static methods ****************************

    /** The empty JMLObjectSet.
     * @see #JMLObjectSet()
     */
    public static final /*@ non_null @*/ JMLObjectSet EMPTY
        = new JMLObjectSet();

    /** Return the singleton set containing the given element.
     * @see #JMLObjectSet(Object)
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.equals(new JMLObjectSet<F>(e));
      @*/
    public static <F> /*@ pure @*/ /*@ non_null @*/
        JMLObjectSet<F> singleton(F e)
    {
        return new JMLObjectSet<F>(e);
    }

    /** Return the set containing all the elements in the given array.
     */
    /*@ public normal_behavior
      @    requires a != null;
      @    ensures \result != null && \result.int_size() == a.length
      @         && (\forall int i; 0 <= i && i < a.length; \result.has(a[i]));
      @*/
    public static <F> /*@ pure @*/ /*@ non_null @*/
        JMLObjectSet<F> convertFrom(/*@ non_null @*/ F[] a)
    {
        /*@ non_null @*/ JMLObjectSet<F> ret = EMPTY;
        for (int i = 0; i < a.length; i++) {
            ret = ret.insert(a[i]);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return the set containing all the object in the
     * given collection.
     *  @throws ClassCastException if some element in c is not an instance of 
     * Object.
     *  @see #containsAll(java.util.Collection)
     */
    /*@   public normal_behavior
      @      requires c != null
      @            && (\forall Object o; c.contains(o);
      @                                  o == null || (o instanceof F));
      @      requires c.size() < Integer.MAX_VALUE;
      @      ensures \result != null && \result.int_size() == c.size()
      @           && (\forall Object x; c.contains(x) <==> \result.has(x));
      @  also
      @    public exceptional_behavior
      @      requires c != null
      @            && (\exists Object o; c.contains(o);
      @                              o != null && !(o instanceof F));
      @      signals_only ClassCastException;
      @*/
    public static <F> /*@ pure @*/ /*@ non_null @*/
        JMLObjectSet<F> convertFrom(/*@ non_null @*/ java.util.Collection<F> c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLObjectSet<F> ret = EMPTY;
        java.util.Iterator<F> celems = c.iterator();
        while (celems.hasNext()) {
            F o = celems.next();
            if (o == null) {
                ret = ret.insert(null);
            } else {
                ret = ret.insert(o);
            }
        }
        return ret;
    } //@ nowarn Exception;

    /** Return the set containing all the object in the
     * given JMLCollection.
     *  @throws ClassCastException if some element in c is not an instance of 
     * Object.
     */
    /*@   public normal_behavior
      @      requires c != null
      @           && (c.elementType <: \type(F));
      @      ensures \result != null
      @           && (\forall Object x; c.has(x) <==> \result.has(x));
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.has(o);
      @                                  !(o instanceof F));
      @      signals_only ClassCastException;
      @*/
    public static <F> /*@ pure @*/ /*@ non_null @*/
        JMLObjectSet<F> convertFrom(/*@ non_null @*/ JMLCollection<F> c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLObjectSet<F> ret = EMPTY;
        JMLIterator<F> celems = c.iterator();
        while (celems.hasNext()) {
            F o = celems.next();
            if (o == null) {
                ret = ret.insert(null);
            } else {
                //@ assume o instanceof Object;
                ret = ret.insert(o);
            }
        }
        return ret;
    } //@ nowarn Exception;

    //**************************** Observers **********************************

    /** Is the argument "==" to one of the
     *  objects in theSet.
     */
    /*@ also
      @   public normal_behavior
      @     requires elem != null;
      @     ensures (* \result <==>
      @       elem is "==" to one of the objects in theSet *);
      @ also
      @   public normal_behavior
      @     requires elem == null;
      @     ensures (* \result <==> null is one of the objects in theSet *);
      @ also
      @   public normal_behavior
      @     requires isEmpty();
      @     ensures ! \result ;
      @*/    
    public /*@ pure @*/ boolean has(Object elem ) {
        return the_list != null && the_list.has(elem);
    }  

    /** Tell whether, for each element in the given collection, there is a
     * "==" element in this set.
     *  @param c the collection whose elements are sought.
     *  @see #isSuperset(JMLObjectSet<E>)
     *  @see #convertFrom(java.util.Collection)
     */
    /*@ public normal_behavior
      @    requires c != null;
      @    ensures \result <==> (\forall Object o; c.contains(o); this.has(o));
      @*/
    public boolean containsAll(/*@ non_null @*/ java.util.Collection<E> c) {
        java.util.Iterator<E> celems = c.iterator();
        while (celems.hasNext()) {
            E o = celems.next();
            if (!has(o)) {
                return false;
            }
        }
        return true;
    }  

    /*@ also
      @   public normal_behavior
      @     ensures \result <==>
      @          s2 != null && s2 instanceof JMLObjectSet
      @          && (\forall Object e; ; this.has(e)
      @                                      == ((JMLObjectSet<E>)s2).has(e));
      @     ensures_redundantly \result ==>
      @             s2 != null && s2 instanceof JMLObjectSet
      @             && containsNull == ((JMLObjectSet<E>)s2).containsNull;
      @*/
    public boolean equals(/*@ nullable @*/ Object s2) {
        return (s2 != null && s2 instanceof JMLObjectSet)
            && (size == ((JMLObjectSet<E>)s2).int_size())
            && isSubset((JMLObjectSet<E>)s2);
    }

    /** Return a hash code for this object.
     */
    public int hashCode() {
        if (size == 0) {
            return 0;
        } else {
            int hash = 0xffff;
            JMLListObjectNode<E> walker = the_list;
            while (walker != null) {
                E wv = walker.val;
                if (wv != null) {
                    hash ^= wv.hashCode();
                }
                walker = walker.next;
            }   
            return hash;
        }
    }

    /** Is the set empty.
     * @see #int_size()
     * @see #has(Object)
     */
    /*@   public normal_behavior
      @     ensures \result == (\forall Object e; ; !this.has(e));
      @ also
      @   protected normal_behavior
      @     ensures the_list == null <==> \result;
      @*/  
    public /*@ pure @*/ boolean isEmpty() {
        return the_list == null;
    }  

    /** Tells the number of elements in the set.
     */
    /*@ also
      @   public normal_behavior
      @    ensures 
      @       (this.isEmpty() ==> \result == 0)
      @       && (!this.isEmpty() ==>
      @             (\exists Object e; this.has(e);
      @                      \result == 1 + (this.remove(e).int_size())) );
      @ implies_that
      @    ensures \result >= 0;
      @*/
    public /*@ pure @*/ int int_size() {
        return size;
    }  

    /** Tells whether this set is a subset of or equal to the argument.
     * @see #isProperSubset(JMLObjectSet<E>)
     * @see #isSuperset(JMLObjectSet<E>)
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @      (\forall Object e; ; this.has(e) ==> s2.has(e));
      @*/  
    public boolean isSubset(/*@ non_null @*/ JMLObjectSet<E> s2) {
        if (size > s2.int_size()) {
            return false;
        } else {
            for (JMLListObjectNode<E> walker = the_list;
                 walker != null;
                 walker = walker.next) {
                if (!s2.has(walker.val)) {
                    return false;
                }
            }   
            //@ assert (\forall Object e; ; this.has(e) ==> s2.has(e));
            return true;
        }   
    }  

    /** Tells whether this set is a subset of but not equal to the
     * argument.
     * @see #isSubset(JMLObjectSet<E>)
     * @see #isProperSuperset(JMLObjectSet<E>)
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result <==>
      @       this.isSubset(s2) && !this.equals(s2);
      @*/    
    public boolean isProperSubset(/*@ non_null @*/ JMLObjectSet<E> s2) {
        return size < s2.int_size() && isSubset(s2);
    }  

    /** Tells whether this set is a superset of or equal to the argument.
     * @see #isProperSuperset(JMLObjectSet<E>)
     * @see #isSubset(JMLObjectSet<E>)
     * @see #containsAll(java.util.Collection)
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result == s2.isSubset(this);
      @*/    
    public boolean isSuperset(/*@ non_null @*/ JMLObjectSet<E> s2) {
        return s2.isSubset(this);
    }

    /** Tells whether this set is a superset of but not equal to the
     * argument.
     * @see #isSuperset(JMLObjectSet<E>)
     * @see #isProperSubset(JMLObjectSet<E>)
     */
    /*@ public normal_behavior
      @    requires s2 != null;
      @    ensures \result == s2.isProperSubset(this);
      @*/
    public boolean isProperSuperset(/*@ non_null @*/ JMLObjectSet<E> s2) {
        return s2.isProperSubset(this);
    }  

    /** Return an arbitrary element of this.
     *  @exception JMLNoSuchElementException if this is empty.
     *  @see #isEmpty()
     *  @see #elements()
     */
    /*@   public normal_behavior
      @      requires !isEmpty();
      @      ensures (\exists Object e; this.has(e);
      @                   (\result == null ==> e == null)
      @                && (\result != null ==> \result == e));
      @ also
      @   public exceptional_behavior
      @     requires isEmpty();
      @     signals_only JMLNoSuchElementException;
      @ implies_that
      @   protected behavior
      @      ensures \result != null ==> \typeof(\result) <: elementType;
      @      ensures !containsNull ==> \result != null;
      @      signals_only JMLNoSuchElementException;
      @      signals (JMLNoSuchElementException) the_list == null;
      @*/
    public E choose() throws JMLNoSuchElementException {
        if (the_list != null) {
            E entry = the_list.val;
            if (entry == null) {
                //@ assume containsNull;
                return null;
            } else {
                E o =  entry ;
                //@ assume o instanceof Object;
                //@ assume \typeof(o) <: elementType;
                return  o;
            }
        } else {
            throw new JMLNoSuchElementException("Tried to .choose() "
                                                + "with JMLObjectSet empty");
        }
    }  

    // ****************** building new JMLObjectSets **************************

    /** Return a clone of this object.  This method does not clone the
     * elements of the set.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null
      @          && \result instanceof JMLObjectSet
      @          && this.equals(\result);
      @*/
    public /*@ non_null @*/ Object clone() { 
        //@ assume owner == null;
        return this;
    }

    /** Returns a new set that contains all the elements of this and
     *  also the given argument.
     *  @see #has(Object)
     *  @see #remove(Object)
     */
    /*@ 
      @  public normal_behavior
      @   requires int_size() < Integer.MAX_VALUE || has(elem);
      @   ensures \result != null
      @	  && (\forall Object e; ;
      @        \result.has(e) <==> this.has(e)
      @                            || (e == null && elem == null)
      @                            || (e != null && e == elem));
      @   ensures_redundantly this.isSubset(\result) && \result.has(elem)
      @     && \result.int_size() == this.int_size() + (this.has(elem) ? 0 : 1);
      @ also public normal_behavior
      @   ensures elem == null ==> \result.containsNull;
      @   ensures elem != null ==> \result.containsNull == containsNull;
      @*/  
    public /*@ non_null @*/ JMLObjectSet<E> insert(E elem)
        throws IllegalStateException
    {
        if (has(elem)) {
            return this;
        } else if (size < Integer.MAX_VALUE) {
            return fast_insert(elem);            
        } else {
            throw new IllegalStateException("Cannot insert into a set "
                                            +"with Integer.MAX_VALUE elements");
        }
    } 

    /** Returns a new set that contains all the elements of this and
     *  also the given argument, assuming the argument is not in the set.
     *  @see #insert(E)
     */
    /*@ protected normal_behavior
      @   requires !has(elem);
      @   requires int_size() < Integer.MAX_VALUE;
      @   ensures \result != null
      @	  && (\forall Object e; ;
      @        \result.has(e) <==> this.has(e)
      @                            || (e == null && elem == null)
      @                            || (e != null && e == elem));
      @   ensures_redundantly this.isSubset(\result) && \result.has(elem)
      @     && \result.int_size() == this.int_size() + 1;
      @*/  
    protected /*@ non_null @*/ JMLObjectSet<E> fast_insert(E elem) {
        return new JMLObjectSet<E>(  // cons() clones if necessary
                                JMLListObjectNode.cons(elem, the_list),
                                size+1);
    }

    /** Returns a new set that contains all the elements of this except for
     *  the given argument.
     *  @see #has(Object)
     *  @see #insert(E)
     */
    /*@ public normal_behavior
      @   ensures \result != null
      @	  && (\forall Object e; ;
      @       \result.has(e) <==>
      @          this.has(e) && !((e == null && elem == null)
      @                           || (e != null && e == elem)));
      @   ensures_redundantly \result.isSubset(this) && !\result.has(elem)
      @      && \result.int_size() == this.int_size() - (this.has(elem) ? 1 : 0);
      @ implies_that
      @    ensures \result != null
      @         && (!containsNull ==> !\result.containsNull);
      @*/
    public /*@ non_null @*/ JMLObjectSet<E> remove(E elem) {
        if (!has(elem)) {
            return this;
        } else {
            //@ assume the_list != null;
            JMLListObjectNode<E> new_list = the_list.remove(elem);
            //@ assume (new_list == null) == (size == 1);
            return new JMLObjectSet<E>(new_list, size - 1);
        }
    } //@ nowarn Post;

    /** Returns a new set that contains all the elements that are in
     *  both this and the given argument.
     *  @see #union(JMLObjectSet)
     *  @see #difference(JMLObjectSet)
     */
    /*@ public normal_behavior
      @   requires s2 != null;
      @   ensures \result != null
      @	  && (\forall Object e; ;
      @            \result.has(e) <==> this.has(e) && s2.has(e));
      @ implies_that
      @    ensures \result != null
      @         && (!containsNull || !s2.containsNull
      @             ==> !\result.containsNull);
      @*/
    public /*@ non_null @*/
        JMLObjectSet<E> intersection(/*@ non_null @*/ JMLObjectSet<E> s2) {
        JMLObjectSet<E> returnSet = new JMLObjectSet<E>();
        JMLListObjectNode<E> thisWalker = the_list;
        while (thisWalker != null) {
            if (s2.has(thisWalker.val)) {
                returnSet = returnSet.fast_insert(thisWalker.val);
            }
            thisWalker = thisWalker.next;
        }   
        return returnSet;
    } //@ nowarn Post;

    /** Returns a new set that contains all the elements that are in
     *  either this or the given argument.
     *  @see #intersection(JMLObjectSet)
     *  @see #difference(JMLObjectSet)
     */
    /*@ public normal_behavior
      @   requires s2 != null;
      @   requires int_size() < Integer.MAX_VALUE - s2.difference(this).int_size();
      @   ensures \result != null
      @	       && (\forall Object e; ;
      @               \result.has(e) <==> this.has(e) || s2.has(e));
      @ implies_that
      @    ensures \result != null
      @         && (!containsNull && !s2.containsNull
      @             ==> !\result.containsNull);
      @*/
    public /*@ non_null @*/
        JMLObjectSet<E> union(/*@ non_null @*/ JMLObjectSet<E> s2)
        throws IllegalStateException
    {
        JMLObjectSet<E> returnSet = s2;
        JMLListObjectNode<E> thisWalker = the_list;
        while (thisWalker != null) {
            returnSet = returnSet.insert(thisWalker.val);
            thisWalker = thisWalker.next;
        }
        return returnSet;
    }  //@ nowarn Post;

    /** Returns a new set that contains all the elements that are in
     *  this but not in the given argument.
     *  @see #union(JMLObjectSet<E>)
     *  @see #difference(JMLObjectSet<E>)
     */
    /*@ public normal_behavior
      @   requires s2 != null;
      @   ensures \result != null
      @	       && (\forall Object e; ;
      @                 \result.has(e) <==> this.has(e) && !s2.has(e));
      @ implies_that
      @    ensures \result != null
      @         && (!containsNull ==> !\result.containsNull);
      @*/
    public /*@ non_null @*/
        JMLObjectSet<E> difference(/*@ non_null @*/ JMLObjectSet<E> s2) {
        JMLObjectSet<E> returnSet = new JMLObjectSet<E>();
        JMLListObjectNode<E> thisWalker = the_list;
        while (thisWalker != null) {
            if (!s2.has(thisWalker.val)) {
                returnSet = returnSet.fast_insert(thisWalker.val);
            }
            thisWalker = thisWalker.next;
        }   
        return returnSet;
    }  //@ nowarn Post;

    /** Returns a new set that is the set of all subsets of this.
     *
     * The implementation is by Tim Wahls.
     */
    /*@ public normal_behavior
      @   requires int_size() < 32;
      @   ensures \result != null
      @	    && (\forall JMLObjectSet<E> s; ;
      @               s.isSubset(this) <==> \result.has(s));
      @   ensures_redundantly \result != null
      @              && (0 < size && size <= 31
      @                  ==> \result.int_size() == (2 << (int_size()-1)));
      @ implies_that
      @    ensures \result != null && !\result.containsNull;
      @ for_example
      @   public normal_example
      @     requires isEmpty();
      @     ensures \result != null && \result.equals(new JMLObjectSet(EMPTY));
      @     ensures_redundantly \result.int_size() == 1;
      @ also
      @   public normal_example
      @     forall Object a, b, c;
      @     requires this.equals(new JMLObjectSet(a).insert(b).insert(c))
      @              && int_size() == 3;
      @     ensures \result != null && \result.int_size() == 8
      @          && \result.has(EMPTY)
      @          && \result.has(new JMLObjectSet<E>(a))
      @          && \result.has(new JMLObjectSet<E>(b))
      @          && \result.has(new JMLObjectSet<E>(c))
      @          && \result.has(new JMLObjectSet<E>(a).insert(b))
      @          && \result.has(new JMLObjectSet<E>(a).insert(c))
      @          && \result.has(new JMLObjectSet<E>(b).insert(c))
      @          && \result.has(new JMLObjectSet<E>(a).insert(b).insert(c));
      @*/
    public /*@ non_null @*/ JMLObjectSet<JMLObjectSet<E>> powerSet()
        throws IllegalStateException
    {
        if (size >= 32) {
            throw new IllegalStateException("Can't compute the powerSet "
                                            + "of such a large set");
        }

        // This a dynamic programming algorithm.

        /*@ non_null @*/ JMLObjectSet<JMLObjectSet<E>> ret
                             = new JMLObjectSet<JMLObjectSet<E>>(JMLObjectSet.EMPTY);
     
        // added is used to make the loop invariant easier to state.
        JMLObjectSet<E> added = new JMLObjectSet<E>();
        JMLIterator<E> elems = iterator();

        //@ loop_invariant !ret.containsNull;
        /*@ maintaining added.isSubset(this) && ret.size >= 1
          @       && (\forall JMLObjectSet s; s.isSubset(added); ret.has(s));
          @  decreasing int_size()-added.int_size();
          @*/
        while (elems.hasNext()) { 
            E cur = elems.next();
            JMLIterator<JMLObjectSet<E>> size_i_and_smaller_subsets = ret.iterator();
            while (size_i_and_smaller_subsets.hasNext()) {
                JMLObjectSet<E> subset = size_i_and_smaller_subsets.next();
                if (cur == null) {
                  ret = ret.insert(subset.insert(null));
                } else {
                  ret = ret.insert(subset.insert(cur));
                }
            }
            added = added.insert(cur);
        }
        return ret;
    }

    /** Return a new JMLObjectBag<E> containing all the elements of this.
     *  @see #toSequence()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall Object o;; 
      @                         \result.count(o) == 1 <==> this.has(o));
      @ implies_that
      @    ensures \result != null && (containsNull <==> \result.containsNull);
      @*/
    public /*@ non_null @*/ JMLObjectBag<E> toBag() {
        JMLObjectBag<E> ret = new JMLObjectBag<E>();
        JMLIterator<E> elems = iterator();
        while (elems.hasNext()) {
            //@ assume elems.moreElements;
            E o = elems.next();
            E e = (o == null ? null : o);
            ret = ret.insert(e);
        }
        return ret;
    } //@ nowarn Exception, Post;

    /** Return a new JMLObjectSequence containing all the elements of this.
     *  @see #toBag()
     *  @see #toArray()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall Object o;; 
      @                         \result.count(o) == 1 <==> this.has(o));
      @ implies_that
      @    ensures \result != null && (containsNull <==> \result.containsNull);
      @*/
    public /*@ non_null @*/ JMLObjectSequence<E> toSequence() {
        JMLObjectSequence<E> ret = new JMLObjectSequence<E>();
        JMLIterator<E> elems = iterator();
        while (elems.hasNext()) {
            //@ assume elems.moreElements;
            E o = elems.next();
            E e = (o == null ? null : o);
            ret = ret.insertFront(e);
        }
        return ret;
    } //@ nowarn Exception, Post;

    /** Return a new array containing all the elements of this.
     *  @see #toSequence()
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.length == int_size()
      @         && (\forall Object o;;
      @                   JMLArrayOps.hasObjectIdentity(\result, o) <==> has(o));
      @    ensures_redundantly \result != null && \result.length == int_size()
      @         && (\forall int i; 0 <= i && i < \result.length;
      @               JMLArrayOps.hasObjectIdentity(\result, \result[i])
      @                    == has(\result[i]));
      @ implies_that
      @    ensures \result != null
      @        && (containsNull <==> !\nonnullelements(\result));
      @*/
    public /*@ non_null @*/ Object[] toArray() {
        Object[] ret = new Object[int_size()];
        JMLIterator<E> elems = iterator();
        int i = 0;
        //@ loop_invariant 0 <= i && i <= ret.length;
        while (elems.hasNext()) {
            //@ assume elems.moreElements && i < ret.length;
            E o = elems.next();
            if (o == null) {
                ret[i] = null;
            } else {
                E e = /**/ o;
                ret[i] =  e ;
            }
            i++;
        }
        return ret;
    } //@ nowarn Exception, Post;

    //********************** Tools Methods *********************************
    // The elements and toString methods are of no value for writing
    // assertions in JML. They are included for the use of developers
    // of CASE tools based on JML, e.g., type checkers, assertion
    // evaluators, prototype generators, test tools, ... . They can
    // also be used in model programs in specifications.

    /** Returns an Enumeration over this set.
     *  @see #iterator()
     */
    /*@  public normal_behavior
      @     ensures \fresh(\result) && this.equals(\result.uniteratedElems);
      @ implies_that
      @    ensures \result != null
      @        && (containsNull == \result.returnsNull);
      @*/
    public /*@ non_null @*/ JMLObjectSetEnumerator<E> elements() {
        return new JMLObjectSetEnumerator<E>(this);
    }  

    /** Returns an Iterator over this set.
     *  @see #elements()
     */
    /*@ also
      @    public normal_behavior
      @      ensures \fresh(\result)
      @          && \result.equals(new JMLEnumerationToIterator<E>(elements()));
      @*/  
    public /*@ non_null @*/ JMLIterator<E> iterator() {
        return new JMLEnumerationToIterator<E>(elements());
    }  //@ nowarn Post;

    /** Return a string representation of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures (* \result is a string representation of this *);
      @*/    
    public /*@ non_null @*/ String toString() {
        String newStr = new String("{");
        JMLListObjectNode<E> setWalker = the_list;
        if (setWalker != null) {
            newStr = newStr + setWalker.val;
            setWalker = setWalker.next;
        }
        while (setWalker != null) {
            newStr = newStr + ", " + setWalker.val;
            setWalker = setWalker.next;
        }   
        newStr = newStr + "}";
        return newStr;
    }
}
