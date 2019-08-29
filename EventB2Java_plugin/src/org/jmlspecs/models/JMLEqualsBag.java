// @(#)$Id: JMLBag.java-generic,v 1.70 2006/12/02 23:38:15 leavens Exp $

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

/** Bags (i.e., multisets) of objects.  This type uses
 * ".equals" to compare elements, and does not clone elements that
 * are passed into and returned from the bag's methods.
 *
 * @version $Revision: 1.70 $
 * @author Gary T. Leavens, with help from Albert Baker, Clyde Ruby,
 * and others.
 * @see JMLCollection
 * @see JMLType
 * @see JMLObjectBag
     * @see JMLValueBag
 * @see JMLEqualsBagEnumerator
 * 
 * @see JMLObjectSet
 * @see JMLValueSet
 */
//-@ immutable
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public /*@ pure @*/ class JMLEqualsBag<E>
     implements JMLCollection<E>
{

    /** The list representing the contents of this bag.  Each element
     * of this list is of type JMLEqualsBagEntry.
     */
    protected final JMLEqualsBagEntryNode<E> the_list;
    //@                  in objectState;
    //@                  maps the_list.elementState \into elementState;

    /** The size of this bag.
     */
    protected /*@ spec_public @*/ final int size;
    //@                                      in objectState;

    //@ protected invariant the_list == null <==> size == 0;
    //@ public    invariant size >= 0;
    /*@ protected invariant the_list != null ==>
      @   (\forall int i; 0 <= i && i < the_list.int_size();
      @			      the_list.itemAt(i) instanceof JMLEqualsBagEntry<E>);
      @*/

    //*********************** equational theory ***********************

    //@ public invariant (\forall E e1; ; count(e1) >= 0);

    /*@ public invariant (\forall JMLEqualsBag<E> s2; s2 != null;
      @                    (\forall E e1, e2; ;
      @                       equational_theory(this, s2, e1, e2) ));
      @*/

    /** An equational specification of the properties of bags.
     */
    /*@ public normal_behavior
       @ {|
       @     // The following are defined by using has and induction.
       @
       @       ensures \result <==>
       @           (new JMLEqualsBag<E>()).count(e1) == 0;
       @     also
       @       requires e1 != null;
       @       ensures \result <==>
       @          s.insert(e1).count(e2) 
       @          	== (e1.equals(e2)
       @                      ? (s.count(e2) + 1) : s.count(e2));
       @     also
       @       ensures \result <==>
       @           s.insert(null).count(e2) 
       @          	== (e2 == null ? (s.count(e2) + 1) : s.count(e2));
       @     also
       @       ensures \result <==>
       @           (new JMLEqualsBag<E>()).int_size() == 0;
       @     also
       @       ensures \result <==>
       @           s.insert(e1).int_size() == (s.int_size() + 1);
       @     also
       @       ensures \result <==>
       @           s.isSubbag(s2)
       @              == (\forall E o; ; s.count(o) <= s2.count(o));
       @     also
       @       ensures \result <==>
       @           s.equals(s2) == ( s.isSubbag(s2) && s2.isSubbag(s));
       @     also
       @       ensures \result <==>
       @           (new JMLEqualsBag<E>()).remove(e1).equals(new JMLEqualsBag());
       @     also
       @       ensures \result <==>
       @           s.insert(null).remove(e2)
       @                     .equals
       @                     (e2 == null ? s : s.remove(e2).insert(null));
       @     also
       @       requires e1 != null;
       @       ensures \result <==>
       @            s.insert(e1).remove(e2)
       @                     .equals
       @                     (e1.equals(e2)
       @                         ? s : s.remove(e2).insert(e1));
       @
       @     // The following are all defined as abbreviations.
       @
       @    also
       @      ensures \result <==>
       @         s.isEmpty() == (s.int_size() == 0);
       @    also
       @      ensures \result <==>
       @           (new JMLEqualsBag<E>()).has(e1);
       @    also
       @      ensures \result <==>
       @         (new JMLEqualsBag<E>(e1)).equals(new JMLEqualsBag()<E>.insert(e1));
       @    also
       @      ensures \result <==>
       @         s.isProperSubbag(s2) == ( s.isSubbag(s2) && !s.equals(s2));
       @    also
       @      ensures \result <==>
       @         s.isSuperbag(s2) == s2.isSubbag(s);
       @    also
       @      ensures \result <==>
       @         s.isProperSuperbag(s2) == s2.isProperSubbag(s);
       @ |}
       @
       @ implies_that   // other ways to specify some operations
       @
       @   ensures \result <==> (new JMLEqualsBag()).isEmpty();
       @
       @   ensures \result <==> !s.insert(e1).isEmpty();
       @
       @   ensures \result <==>
       @         (new JMLEqualsBag<E>(null)).has(e2) == (e2 == null);
       @
       @   ensures \result <==>
       @         (e1 != null
       @          ==> new JMLEqualsBag<E>(e1).has(e2)
       @                        == (e1.equals(e2)));
       public pure model boolean equational_theory(JMLEqualsBag<E> s,
                                                   JMLEqualsBag<E> s2,
                                                   E e1,
                                                   E e2);
       @*/ // end of equational_theory

    //@ public invariant elementType <: \type(E);
    /*@ public invariant
      @           (\forall E o; o != null && has(o);
      @                                 \typeof(o) <: elementType);
      @*/

    //@ public invariant_redundantly isEmpty() ==> !containsNull;

    //@ public invariant owner == null;

    //************************* Constructors ********************************

    /** Initialize this bag to be empty.
     *  @see #EMPTY
     */
    /*@ public normal_behavior
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures this.isEmpty();
      @    ensures_redundantly (* this is an empty bag *);
      @
      @ implies_that
      @    ensures elementType <: \type(Object) && !containsNull;
      @*/
    public JMLEqualsBag() {
        //@ set owner = null;
        the_list = null;
        size = 0;
        //@ set elementType = \type(E);
        //@ set containsNull = false;
    }  

    /*@ public normal_behavior
      @    assignable objectState, elementType, containsNull, owner;
      @    ensures count(elem) == 1 && int_size() == 1;
      @    ensures_redundantly (* this is a singleton bag containing elem *);
      @
      @ implies_that
      @    ensures containsNull <==> elem == null;
      @    ensures elem != null ==> elementType == \typeof(elem);
      @    ensures elem == null ==> elementType <: \type(E);
      @*/
    /** Initialize this bag to contain the given element.
     *  @param elem the element that is the sole contents of this bag.
     *  @see #singleton
     */
    public JMLEqualsBag (E elem) {
        //@ set owner = null;
        // cons() clones if necessary
        the_list = JMLEqualsBagEntryNode.cons(new JMLEqualsBagEntry<E>(elem),
                                              null);
        size = 1;
        //@ set elementType = the_list.entryElementType;
        //@ assume elem != null ==> elementType == \typeof(elem);
        //@ set containsNull = (elem == null);
    }  

    /** Initialize this bag with the given representation.
     */
    /*@  requires ls == null <==> sz == 0;
      @  requires sz >= 0;
      @  assignable objectState, elementType, containsNull, owner;
      @  ensures elementType
      @          == (ls == null ? \type(Object) : ls.entryElementType);
      @  ensures containsNull
      @          == (ls == null ? false : ls.containsNullElements);
      @*/
    protected JMLEqualsBag (JMLEqualsBagEntryNode<E> ls, int sz) {
        //@ set owner = null;
        the_list = ls;
        size = sz;
        /*@ set elementType
          @     = (ls == null ? \type(Object) : ls.entryElementType);
          @ set containsNull = (ls == null ? false : ls.containsNullElements);
          @*/
    }

    //**************************** Static methods ****************************

    /** The empty JMLEqualsBag.
     *  @see #JMLEqualsBag()
     */
    public static final /*@ non_null @*/ JMLEqualsBag EMPTY
        = new JMLEqualsBag();

    /** Return the singleton bag containing the given element.
     *  @see #JMLEqualsBag(E)
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.equals(new JMLEqualsBag<F>(e));
      @*/
    public static <F> /*@ pure @*/ /*@ non_null @*/ JMLEqualsBag<F> singleton(
        F e)
    {
        return new JMLEqualsBag<F>(e);
    }

    /** Return the bag containing all the elements in the given array.
     */
    /*@ public normal_behavior
      @    requires a != null;
      @    ensures \result != null && \result.int_size() == a.length
      @         && (* \result contains each element in a *);
      @    ensures_redundantly \result != null && \result.int_size() == a.length
      @         && (\forall int i; 0 <= i && i < a.length; \result.has(a[i]));
      @*/
    public static <F> /*@ pure @*/ /*@ non_null @*/
        JMLEqualsBag<F> convertFrom(/*@ non_null @*/F[] a)
    {
        /*@ non_null @*/ JMLEqualsBag<F> ret = EMPTY;
        for (int i = 0; i < a.length; i++) {
            ret = ret.insert(a[i]);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return the bag containing all the object in the
     * given collection.
     *  @throws ClassCastException if some element in c is not an instance of 
     * Object.
     *  @see #containsAll(java.util.Collection)
     */
    /*@   public normal_behavior
      @      requires c != null
      @           && (c.elementType <: \type(Object));
      @      ensures \result != null && \result.int_size() == c.size()
      @           && (* \result contains each element in c *);
      @      ensures_redundantly \result != null && \result.int_size() == c.size()
      @           && (\forall Object x; c.contains(x) <==> \result.has(x));
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.contains(o);
      @                                  !(o instanceof Object));
      @      signals_only ClassCastException;
      @*/
    public static <F> /*@ pure @*/ /*@ non_null @*/
        JMLEqualsBag<F> convertFrom(/*@ non_null @*/ java.util.Collection<F> c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLEqualsBag<F> ret = EMPTY;
        java.util.Iterator<F> celems = c.iterator();
        while (celems.hasNext()) {
            F o = celems.next();
            if (o == null) {
                ret = ret.insert(null);
            } else {
                //@ assume o instanceof Object;
//                ret = ret.insert(o);
                ret = ret.insert(o);
            }
        }
        return ret;
    } //@ nowarn Exception;

    /** Return the bag containing all the object in the
     * given JMLCollection.
     *  @throws ClassCastException if some element in c is not an instance of 
     * Object.
     */
    /*@   public normal_behavior
      @      requires c != null
      @           && (c.elementType <: \type(Object));
      @      ensures \result != null
      @           && (\forall Object x; c.has(x) <==> \result.has(x));
      @      ensures_redundantly \result.int_size() == c.int_size();
      @  also
      @    public exceptional_behavior
      @      requires c != null && (\exists Object o; c.has(o);
      @                                  !(o instanceof Object));
      @      signals_only ClassCastException;
      @*/
    public static <F> /*@ pure @*/ /*@ non_null @*/
        JMLEqualsBag<F> convertFrom(/*@ non_null @*/ JMLCollection<F> c)
        throws ClassCastException
    {
        /*@ non_null @*/ JMLEqualsBag<F> ret = EMPTY;
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

    /** Tell how many times the given element occurs ".equals"
     *  to an element in this bag.
     *  @param elem the element sought.
     *  @return the number of times elem occurs in this bag.
     *  @see #has(Object)
     */
    /*@ 
      @    public normal_behavior
      @      ensures \result >= 0
      @           && (* \result is the number of times elem occurs in this *);
      @*/
     //@ implies_that
     //@    ensures \result >= 0;
    public int count(E elem ) { // ???
        JMLEqualsBagEntry<E> matchingEntry = getMatchingEntry(elem);
        if (matchingEntry != null) {
            return matchingEntry.count;
        } else {
            //@ assert !has(elem); 
            // there is no matching item in the list.
            return 0;
        }
    }  

    /** Tell whether the given element occurs ".equals"
     *  to an element in this bag.
     *  @param elem the element sought.
     *  @see #count(Object)
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result <==> (count(elem) > 0);
      @*/
    public boolean has(Object elem) {
		try {
			E insert = (E) elem;
        	return the_list != null && the_list.has(new JMLEqualsBagEntry<E>(insert));
		} catch (ClassCastException e) {
			return false;
		}
    }  

    /** Tell whether, for each element in the given collection, there is a
     * ".equals" element in this bag.
     *  @param c the collection whose elements are sought.
     *  @see #isSuperbag(JMLEqualsSet)
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

    /** Test whether this object's value is equal to the given argument.
     * This comparison uses ".equals" to compare elements.
     *
     * <p>Note that the <kbd>elementType</kbd>s may be different for
     * otherwise equal bags.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result <==>
      @              b2 != null && b2 instanceof JMLEqualsBag<E>
      @               && (\forall Object e; ;
      @                   this.count(e) == ((JMLEqualsBag<E>)b2).count(e));
      @*/
    /*@ implies_that
      @   public normal_behavior
      @     requires b2 != null && b2 instanceof JMLEqualsBag<E>;
      @     ensures \result ==>
      @          this.int_size() == ((JMLEqualsBag<E>)b2).int_size()
      @          && containsNull == ((JMLEqualsBag<E>)b2).containsNull;
      @*/
    public boolean equals(/*@ nullable @*/ Object b2) {
        return b2 != null && b2 instanceof JMLEqualsBag
            && (size == ((JMLEqualsBag<E>)b2).int_size())
            && isSubbag((JMLEqualsBag<E>)b2);
    }  

    /** Return a hash code for this object
     */
    public /*@ pure @*/ int hashCode() {
        return the_list == null ? 0 : the_list.hashCode();
    }

    /** Tell whether this bag has no elements.
     * @see #int_size()
     * @see #has(Object)
     */
    /*@ public normal_behavior
      @   ensures \result == (\forall E e; ; count(e) == 0);
      @*/
    public boolean isEmpty() {
        return the_list == null;
    }  

    /** Tell the number of elements in this bag.
     */
    /*@ also
      @    public normal_behavior
      @      ensures \result >= 0 && (* \result is the size of this bag *);
      @*/
    public int int_size( ) {
        return size;
    }  

    /** Tells whether every item in this bag is contained in the argument.
     * @see #isProperSubbag(JMLEqualsBag<E>)
     * @see #isSuperbag(JMLEqualsBag<E>)
     */
    /*@ public normal_behavior
      @    requires b2 != null;
      @    ensures \result <==>
      @      (\forall E e; ; count(e) <= b2.count(e));
      @*/
    public boolean isSubbag(/*@ non_null @*/ JMLEqualsBag<E> b2) {
        if (size > b2.int_size()) {
            return false;
        } else {
            for (JMLListValueNode<JMLEqualsBagEntry<E>> walker = the_list;
                 walker != null;
                 walker = walker.next) {
                //@ assume walker.val instanceof JMLEqualsBagEntry;
                JMLEqualsBagEntry<E> entry =  walker.val;
                if (entry.count > b2.count(entry.theElem)) {
                    return false;
                }
            }   
            //@ assert (\forall Object e; ; this.count(e) <= b2.count(e));
            return true;
        }
    }

    /** Tells whether every item in this bag is contained in the
     * argument, but the argument is strictly larger.
     * @see #isSubbag(JMLEqualsBag<E>)
     * @see #isProperSuperbag(JMLEqualsBag<E>)
     */
    /*@ public normal_behavior
      @    requires b2 != null;
      @    ensures \result <==>
      @       this.isSubbag(b2) && !this.equals(b2);
      @*/
    public boolean isProperSubbag(/*@ non_null @*/ JMLEqualsBag<E> b2) {
        return size < b2.int_size() && isSubbag(b2);
    }  

    /** Tells whether every item in the argument is contained in this bag.
     * @see #isProperSuperbag(JMLEqualsBag<E>)
     * @see #isSubbag(JMLEqualsBag<E>)
     * @see #containsAll(java.util.Collection)
     */
    /*@ public normal_behavior
      @    requires b2 != null;
      @    ensures \result == b2.isSubbag(this);
      @*/
    public boolean isSuperbag(/*@ non_null @*/ JMLEqualsBag<E> b2) {
        return b2.isSubbag(this);
    }

    /** Tells whether every item in the argument is contained in this bag
     * argument, but this bag is strictly larger.
     * @see #isSuperbag(JMLEqualsBag<E>)
     * @see #isProperSubbag(JMLEqualsBag<E>)
     */
    /*@  public normal_behavior
      @    requires b2 != null;
      @    ensures \result == b2.isProperSubbag(this);
      @*/
    public boolean isProperSuperbag(/*@ non_null @*/ JMLEqualsBag<E> b2) {
        return b2.isProperSubbag(this);
    }  

    /** Return an arbitrary element of this.
     *  @exception JMLNoSuchElementException if this is empty.
     *  @see #isEmpty()
     *  @see #elements()
     */
    /*@   public normal_behavior
      @     requires !isEmpty();
      @     ensures (\exists E e; this.has(e);
      @                       \result.equals(e));
      @ also
      @   public exceptional_behavior
      @     requires isEmpty();
      @     signals_only JMLNoSuchElementException;
      @
      @ implies_that
      @    ensures \result != null ==> \typeof(\result) <: elementType;
      @    ensures !containsNull ==> \result != null;
      @    signals_only JMLNoSuchElementException;
      @    signals (JMLNoSuchElementException) size == 0;
      @*/
    public E choose() throws JMLNoSuchElementException {
        if (the_list != null) {
            //@ assume the_list.val instanceof JMLEqualsBagEntry;
            JMLEqualsBagEntry<E> entry = the_list.val;
            E elt = entry.theElem;
            if (elt == null) {
                //@ assume containsNull;
                return null;
            } else {
                E o = elt;
                //@ assume o != null && \typeof(o) <: elementType;
                return  o;
            }
        } else {
            throw new JMLNoSuchElementException("Tried to .choose() "
                                                + "with JMLEqualsBag empty");
        }
    }  

    // ******************** building new JMLEqualsBags **********************

    /** Return a clone of this object.  This method does not clone the
     * elements of the bag.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof JMLEqualsBag && this.equals(\result);
      @     ensures_redundantly \result != null;
      @*/
    public /*@ non_null @*/ Object clone() { 
        return this;
    }  

    /** Find a JMLEqualsBagEntry that is for the same element, if possible.
     *  @param item the item sought.
     *  @return null if the item is not in the bag.
     */
    /*@  assignable \nothing;
      @   ensures the_list == null ==> \result == null;
      @  ensures_redundantly \result != null ==> the_list != null;
      @   ensures \result != null
      @        ==> 0 <= \result.count && \result.count <= size;
      @*/
    protected JMLEqualsBagEntry<E> getMatchingEntry(E item) {
        JMLEqualsBagEntry<E> currEntry = null;
        JMLListValueNode<JMLEqualsBagEntry<E>> ptr = this.the_list;
        //@ maintaining (* no earlier element matches item *);
        while (ptr != null) {
            //@ assume ptr.val instanceof JMLEqualsBagEntry;
            currEntry = (JMLEqualsBagEntry<E>) ptr.val;
            if (currEntry.equalElem(item)) {
                //@ assume currEntry.count <= size;
                return currEntry;
            }
            ptr = ptr.next;
        }
        return null;
    }

    /** Return a bag containing the given item and the ones in
     * this bag.
     *  @see #insert(Object, int)
     *  @see #has(Object)
     *  @see #remove(Object)
     */
    /*@ 
      @   public normal_behavior
      @    requires size < Integer.MAX_VALUE;
      @    {|
      @       requires elem != null;
      @       ensures \result != null
      @       && (\forall Object e; ;
      @                ( (e.equals(elem))
      @    	        ==> \result.count(e) == count(e) + 1 )
      @             && ( !(e.equals(elem))
      @    	        ==> \result.count(e) == count(e) ));
      @     also
      @       requires elem == null;
      @       ensures \result != null
      @       && (\forall Object e; ;
      @               ( e == null
      @    	    ==> \result.count(e) == count(e) + 1 )
      @            && (e != null
      @    	    ==> \result.count(e) == count(e) ));
      @    |}
      @*/
    public /*@ non_null @*/ JMLEqualsBag<E> insert(/*@ nullable @*/ E elem)
        throws IllegalStateException
    {
        return insert(elem, 1);
    }

    /** Return a bag containing the given item the given number of
     *  times, in addition to the ones in this bag.
     *  @see #insert(Object)
     *  @see #has(Object)
     *  @see #remove(Object, int)
     */
    /*@ 
      @   public normal_behavior
      @    requires cnt > 0;
      @    requires size <= Integer.MAX_VALUE - cnt;
      @    {|
      @       requires elem != null;
      @       ensures \result != null
      @	      && (\forall Object e; ;
      @                ( (e != null && e.equals(elem))
      @	                  ==> \result.count(e) == count(e) + cnt )
      @             && ( e == null || !(e.equals(elem))
      @	                 ==> \result.count(e) == count(e) ));
      @     also
      @       requires elem == null;
      @       ensures \result != null
      @	      && (\forall Object e; ;
      @	              ( e == null ==> \result.count(e) == count(e) + cnt )
      @	           && ( e != null ==> \result.count(e) == count(e) ));
      @    |}
      @ also
      @  public normal_behavior
      @    requires cnt == 0;
      @    ensures \result != null && \result.equals(this);
      @*/
    //@ also
    //@      signals (IllegalArgumentException) cnt < 0;
    public /*@ non_null @*/ JMLEqualsBag<E> insert(/*@ nullable @*/ E elem, int cnt)
          throws IllegalArgumentException, IllegalStateException
    {
        if (cnt < 0) {
            throw new IllegalArgumentException("insert called with negative count");
        }
        if (cnt == 0) {
            return this;
        }
        if (!(size <= Integer.MAX_VALUE - cnt)) {
            throw new IllegalStateException("Bag too big to insert into");
        }

        //@ assume cnt > 0;
        JMLEqualsBagEntry<E> entry = null;
        JMLEqualsBagEntryNode<E> new_list = the_list;
        JMLEqualsBagEntry<E> matchingEntry = getMatchingEntry(elem);
        if (matchingEntry != null) {
            entry = new JMLEqualsBagEntry<E>(matchingEntry.theElem,
                                          matchingEntry.count + cnt);
            JMLListValueNode<JMLEqualsBagEntry<E>> nl = the_list.removeBE(matchingEntry);
            if (nl == null) {
                new_list = null;
            } else {
                new_list = (JMLEqualsBagEntryNode<E>) nl;
            }
        } else {
            //@ assert !has(elem); 
            // there is no matching item in the list.
            entry = new JMLEqualsBagEntry<E>(elem, cnt);
        }
        // cons() clones if necessary
        return new JMLEqualsBag<E>(JMLEqualsBagEntryNode.cons(entry, new_list),
                                size + cnt);
    }

    /** Return a bag containing the items in this bag except for
     * one of the given element.
     * @see #remove(E, int)
     * @see #insert(E)
     */
    /*@ public normal_behavior
      @ {|
      @    requires elem != null;
      @    ensures \result != null
      @	   && (\forall E e; ;
      @             ( (e.equals(elem) && has(e))
      @		  ==> \result.count(e) == count(e) - 1 )
      @          && ( !(e.equals(elem))
      @		  ==> \result.count(e) == count(e) ));
      @  also
      @    requires elem == null;
      @    ensures \result != null
      @	   && (\forall E e; ;
      @	           ( e == null
      @		  ==> \result.count(e) == count(e) - 1 )
      @	        && (e != null
      @		  ==> \result.count(e) == count(e) ));
      @ |}
      @*/
    public /*@ non_null @*/ JMLEqualsBag<E> remove(/*@ nullable @*/ E elem) {
        return remove(elem, 1);
    }

    /** Return a bag containing the items in this bag, except for
     *  the given number of the given element.
     * @see #remove(E)
     * @see #insert(E, int)
     */
    /*@ public normal_behavior
      @  requires cnt > 0;
      @  {|
      @     requires elem != null;
      @     ensures \result != null
      @	    && (\forall E e; ;
      @              ( (e.equals(elem) && has(e))
      @		   ==> \result.count(e) == JMLMath.max(0, count(e) - cnt) )
      @           && ( !(e.equals(elem))
      @		   ==> \result.count(e) == count(e) ));
      @   also
      @     requires elem == null;
      @     ensures \result != null
      @	    && (\forall E e; ;
      @	            ( e == null
      @		   ==> \result.count(e) == JMLMath.max(0, count(e) - cnt) )
      @	         && (e != null
      @		   ==> \result.count(e) == count(e) ));
      @  |}
      @ also
      @  public normal_behavior
      @    requires cnt == 0;
      @    ensures \result != null && \result.equals(this);
      @ implies_that
      @    requires 0 <= cnt;
      @*/
    public /*@ non_null @*/ JMLEqualsBag<E> remove(/*@ nullable @*/ E elem, int cnt)
        throws IllegalArgumentException
    {
        if (cnt < 0) {
            throw new IllegalArgumentException("remove called with negative count");
        }
        if (cnt == 0) {
            return this;
        }

        JMLEqualsBagEntry<E> entry = null;
        JMLEqualsBagEntryNode<E> new_list = the_list;
        JMLEqualsBagEntry<E> matchingEntry = getMatchingEntry(elem);
        if (matchingEntry != null) {
            JMLListValueNode<JMLEqualsBagEntry<E>> nl = the_list.removeBE(matchingEntry);
            if (nl == null) {
                new_list = null;
            } else {
                new_list = (JMLEqualsBagEntryNode<E>) nl;
            }
            //@ assume new_list == null <==> matchingEntry.count == size;
            if ((matchingEntry.count - cnt) > 0) {
                entry = new JMLEqualsBagEntry<E>(matchingEntry.theElem,
                                              matchingEntry.count - cnt);
                // cons() clones if necessary
                return new JMLEqualsBag<E>(JMLEqualsBagEntryNode.cons(entry,
                                                                   new_list),
                                        size-cnt);
            } else {
                return new JMLEqualsBag<E>(new_list,
                                        size - matchingEntry.count);
            }
        } else {
            //@ assert !has(elem); 
            // there is no matching item in the list.
            return this;
        }
    }  

    /** Return a bag containing the items in this bag, except for
     *  all items that are ".equals" to the given item.
     *  @see #remove(E)
     *  @see #remove(E, int)
     */
    /*@   public normal_behavior
      @     requires elem != null;
      @     ensures \result != null
      @	    && (\forall E e; ;
      @              ( (e.equals(elem) && has(e))
      @		   ==> \result.count(e) == 0 )
      @           && ( !(e.equals(elem))
      @		   ==> \result.count(e) == count(e) ));
      @ also
      @   public normal_behavior
      @     requires elem == null;
      @     ensures \result != null
      @	    && (\forall E e; ;
      @	            ( e == null
      @		   ==> \result.count(e) == 0 )
      @	         && (e != null
      @		   ==> \result.count(e) == count(e) ));
      @*/
    public /*@ non_null @*/ JMLEqualsBag<E> removeAll(/*@ nullable @*/ E elem) {
        JMLEqualsBagEntry<E> matchingEntry = getMatchingEntry(elem);
        if (matchingEntry != null) {
            //@ assert the_list != null;
            JMLListValueNode<JMLEqualsBagEntry<E>> nl = the_list.removeBE(matchingEntry);
            JMLEqualsBagEntryNode<E> new_list;
            if (nl == null) {
                new_list = null;
            } else {
                new_list = (JMLEqualsBagEntryNode<E>) nl;
            }
            //@ assume new_list == null <==> size-matchingEntry.count == 0;
            return new JMLEqualsBag<E>(new_list, size - matchingEntry.count);
        } else {
            //@ assert !has(elem); 
            // there is no matching item in the list.
            return this;
        }
    }  

    /** Return a bag containing the items in both this bag and the
     *  given bag.  Note that items occur the minimum number of times they
     *  occur in both bags.
     *  @see #union(JMLEqualsBag<E>)
     *  @see #difference(JMLEqualsBag<E>)
     */
    /*@ public normal_behavior
      @    requires b2 != null;
      @    ensures \result != null
      @	   && (\forall Object e; ;
      @             \result.count(e) == Math.min(count(e), b2.count(e)));
      @*/
    public /*@ non_null @*/ 
        JMLEqualsBag<E> intersection(/*@ non_null @*/ JMLEqualsBag<E> b2)
    {
        JMLEqualsBagEntryNode<E> newList = null;
        JMLEqualsBagEntry<E> newEntry;
        int othCount, newCount;
        int newSize = 0;
        JMLListValueNode<JMLEqualsBagEntry<E>> thisWalker = the_list;
        while (thisWalker != null) {
            //@ assume thisWalker.val instanceof JMLEqualsBagEntry;
            JMLEqualsBagEntry<E> currEntry = (JMLEqualsBagEntry<E>) thisWalker.val;
            othCount = b2.count(currEntry.theElem);
            newCount = Math.min(othCount, currEntry.count);
            if (newCount >= 1) {
                newEntry = new JMLEqualsBagEntry<E>(currEntry.theElem, newCount);
                newList = new JMLEqualsBagEntryNode<E>(newEntry, newList);
                newSize += newCount;
            }
            thisWalker = thisWalker.next;
        }   
        return new JMLEqualsBag<E>(newList, newSize);
    }  

    /** Return a bag containing the items in either this bag or the
     *  given bag.  Note that items occur the sum of times they
     *  occur in both bags.
     *  @see #intersection(JMLEqualsBag<E>)
     *  @see #difference(JMLEqualsBag<E>)
     */
    /*@ public normal_behavior
      @    requires size < Integer.MAX_VALUE - b2.size;
      @    requires b2 != null;
      @    ensures \result != null
      @	   && (\forall E e; ;
      @             \result.count(e) == (count(e) + b2.count(e)));
      @*/
    public /*@ non_null @*/ 
        JMLEqualsBag<E> union(/*@ non_null @*/ JMLEqualsBag<E> b2)
    {
        JMLEqualsBagEntryNode<E> newList = null;
        JMLEqualsBagEntry<E> newEntry;
        int othCount, newCount;
        JMLListValueNode<JMLEqualsBagEntry<E>> thisWalker = the_list;
        while (thisWalker != null) {
            //@ assume thisWalker.val instanceof JMLEqualsBagEntry;
            JMLEqualsBagEntry<E> currEntry = (JMLEqualsBagEntry<E>) thisWalker.val;
            othCount = b2.count(currEntry.theElem);
            newCount = currEntry.count + othCount;
            //@ assume newCount > 0;
            newEntry = new JMLEqualsBagEntry<E>(currEntry.theElem, newCount);
            newList = new JMLEqualsBagEntryNode<E>(newEntry, newList);
            thisWalker = thisWalker.next;
        }   
        /*@ assert newList != null
          @      ==> (\forall JMLEqualsBagEntry<E> e; the_list.has(e);
          @             (\exists JMLEqualsBagEntry<E> n; newList.has(n);
          @                 n.theElem.equals(e.theElem) ==>
          @                 n.count == e.count + b2.count(e.theElem)));
          @*/
        JMLListValueNode<JMLEqualsBagEntry<E>> othWalker = b2.the_list;
        while (othWalker != null) {
            //@ assume othWalker.val instanceof JMLEqualsBagEntry;
            JMLEqualsBagEntry<E> currEntry = (JMLEqualsBagEntry<E>) othWalker.val;
            if (the_list == null || !the_list.has(currEntry)) {
                newList = new JMLEqualsBagEntryNode<E>(currEntry, newList);
            }
            othWalker = othWalker.next;
        }
        return new JMLEqualsBag<E>(newList, size + b2.size);
    }  

    /** Return a bag containing the items in this bag minus the
     *  items in the given bag.  If an item occurs in this bag N times,
     *  and M times in the given bag, then it occurs N-M times in the result.
     *  @see #union(JMLEqualsBag<E>)
     *  @see #difference(JMLEqualsBag<E>)
     */
    /*@ public normal_behavior
      @   requires b2 != null;
      @   ensures \result != null
      @	  && (\forall E e; ;
      @            \result.count(e) == JMLMath.max(0, count(e) - b2.count(e)));
      @*/
    public /*@ non_null @*/ JMLEqualsBag<E> 
        difference(/*@ non_null @*/ JMLEqualsBag<E> b2)
    {
        JMLEqualsBagEntryNode<E> newList = null;
        JMLEqualsBagEntry<E> newEntry;
        int othCount, newCount;
        int newSize = 0;
        JMLListValueNode<JMLEqualsBagEntry<E>> thisWalker = the_list;
        while (thisWalker != null) {
            //@ assume thisWalker.val instanceof JMLEqualsBagEntry;
            JMLEqualsBagEntry<E> currEntry = (JMLEqualsBagEntry<E>) thisWalker.val;
            othCount = b2.count(currEntry.theElem);
            newCount = Math.max(0, currEntry.count - othCount);
            if (newCount >= 1) {
                newEntry = new JMLEqualsBagEntry<E>(currEntry.theElem, newCount);
                newList = new JMLEqualsBagEntryNode<E>(newEntry, newList);
                newSize += newCount;
            }
            thisWalker = thisWalker.next;
        }   
        return new JMLEqualsBag<E>(newList, newSize);
    }  


    /** Return a new JMLEqualsSequence containing all the elements of this.
     *  @see #toArray()
     *  @see #toSet()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall E o;; \result.count(o) == this.count(o));
      @*/
    public /*@ non_null @*/ JMLEqualsSequence<E> toSequence() {
        JMLEqualsSequence<E> ret = new JMLEqualsSequence<E>();
        JMLIterator<E> elems = iterator();
        while (elems.hasNext()) {
            //@ assume elems.moreElements;
            E o = elems.next();
            E e = (o == null ? null : o);
            ret = ret.insertFront(e);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return a new JMLEqualsSet<E> containing all the elements of this.
     *  @see #toSequence()
     */
    /*@ public normal_behavior
      @    ensures \result != null
      @         && (\forall E o;; \result.has(o) == this.has(o));
      @*/
    public /*@ non_null @*/ JMLEqualsSet<E> toSet() {
        JMLEqualsSet<E> ret = new JMLEqualsSet<E>();
        JMLIterator<E> elems = iterator();
        while (elems.hasNext()) {
            //@ assume elems.moreElements;
            E o = elems.next();
            E e = (o == null ? null : o);
            ret = ret.insert(e);
        }
        return ret;
    } //@ nowarn Exception;

    /** Return a new array containing all the elements of this.
     *  @see #toSequence()
     */
    /*@ public normal_behavior
      @    ensures \result != null && \result.length == int_size()
      @         && (\forall E o;;
      @                   JMLArrayOps.valueEqualsCount(\result, o) == count(o));
      @    ensures_redundantly \result != null && \result.length == int_size()
      @         && (\forall int i; 0 <= i && i < \result.length;
      @               JMLArrayOps.valueEqualsCount(\result, \result[i])
      @                    == count(\result[i]));
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
                E e =  o;
                ret[i] =  e;
            }
            i++;
        }
        return ret;
    } //@ nowarn Exception;

    // ********************* Tools Methods *********************************
    // The enumerator method and toString are of no value for writing
    // assertions in JML. They are included for the use of developers
    // of CASE tools based on JML, e.g., type checkers, assertion
    // evaluators, prototype generators, test tools, ... . They can
    // also be used in model programs in specifications.

    /** Returns an Enumeration over this bag.
     *  @see #iterator()
     */
    /*@ public normal_behavior
      @   ensures \fresh(\result) && this.equals(\result.uniteratedElems);
      @*/  
	public /*@ non_null @*/ JMLEqualsBagEnumerator<E> elements() {
        return new JMLEqualsBagEnumerator<E>(this);
    }  

    /** Returns an iterator over this bag.
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
        JMLListValueNode<JMLEqualsBagEntry<E>> bagWalker = the_list;

        if (bagWalker != null) {
            newStr = newStr + bagWalker.val;
            bagWalker = bagWalker.next;
        }
        while (bagWalker != null) {
            newStr = newStr + ", " + bagWalker.val;
            bagWalker = bagWalker.next;
        }   
        newStr = newStr + "}";
        return newStr;
    }
}  // end of class JMLEqualsBag


/** Internal class used in the implementation of JMLEqualsBag.
 *
 *  @author Gary T. Leavens
 *  @see JMLEqualsBag
 *  @see JMLEqualsBagEntryNode
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
/*@ pure spec_public @*/ class JMLEqualsBagEntry<E> implements JMLType {

    /** The element in this bag entry.
     */
    public final E theElem;

    /** The number of times the element occurs.
     */
    public final int count;

    //@ public invariant count > 0;

    /** The type of the element in this entry.  This is E if
     *  the element is null.
     */
    //@ ghost public \TYPE elementType;

    //@ public invariant elementType <: \type(E);

    /*@ public
      @   invariant (theElem == null ==> elementType == \type(E))
      @          && (theElem != null ==> elementType == \typeof(theElem));
      @*/

    //@ public invariant owner == null;

    /** Initialize this object to be a singleton entry.
     */
    /*@ public normal_behavior
      @   assignable theElem, count, elementType, owner;
      @   ensures theElem == e && count == 1;
      @*/
    public JMLEqualsBagEntry(E e) {
        //@ set owner = null;
        theElem = e;
        count = 1;
        /*@ set elementType
          @     = (theElem == null ? \type(E) : \typeof(theElem));
          @*/
    }

    /** Initialize this object to be for the given element with the
     *  given number of repetitions.
     */
    /*@ public normal_behavior
      @    requires cnt > 0;
      @   assignable theElem, count, elementType, owner;
      @    ensures count == cnt && (e == null ==> theElem == null);
      @   ensures (e != null ==> e.equals(theElem));
      @*/
    public JMLEqualsBagEntry(E e, int cnt) {
        //@ set owner = null;
        theElem = e;
        count = cnt;
        /*@ set elementType
          @     = (theElem == null ? \type(E) : \typeof(theElem));
          @*/
    }

    /** Make a clone of the given entry.
     */
    public /*@ non_null @*/ Object clone() {
        //@ assume owner == null;
        return this;
    }   

    /** Are these elements equal? */
    /*@ public normal_behavior
      @    ensures \result <==>
      @         (othElem == null && theElem == null)
      @      || (othElem != null && othElem.equals(theElem));
      @*/
    public boolean equalElem(E othElem) {
        return (othElem == null && theElem == null)
            || (othElem != null && othElem.equals(theElem));
    }   

    /** Test whether this object's value is equal to the given argument.
     */
    public boolean equals(/*@ nullable @*/ Object obj) {
        if (obj != null && obj instanceof JMLEqualsBagEntry) {
            JMLEqualsBagEntry<E> oth = (JMLEqualsBagEntry<E>)obj;
            return equalElem(oth.theElem);
        } else {
            return(false);
        }
    }   

    /** Return a hash code for this object.
     */
    public int hashCode() {
        return theElem == null ? 0 : theElem.hashCode();
    }

    /** Return a new bag entry with the same element as this but with
     *  the given number of repetitions added to the element's current
     *  count.
     */
    /*@ public normal_behavior
      @   requires numInserted > 0;
      @   ensures \result != null && \result.count == count + numInserted;
      @   ensures \result != null && \result.theElem.equals(theElem);
      @*/
    public JMLEqualsBagEntry<E> insert(int numInserted) {
        return new JMLEqualsBagEntry<E>(theElem, count + numInserted);
    }  

    /** Return a string representation of this object.
     */
    public /*@ non_null @*/ String toString() {
        if (count == 1) {
            return theElem + "";
        } else {
            return count + " copies of " + theElem;
        }
    }   

}
/** Internal class used in the implementation of JMLEqualsBag<E>.
 *
 *  @author Gary T. Leavens
 *  @see JMLEqualsBag
 *  @see JMLEqualsBagEntry<E>
 *  @see JMLListValueNode
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
/*@ pure spec_public @*/ class JMLEqualsBagEntryNode<E> extends JMLListValueNode<JMLEqualsBagEntry<E>> {

    //@ public invariant elementType == \type(JMLEqualsBagEntry<E>) && !containsNull;

    //@ public invariant val != null && val instanceof JMLEqualsBagEntry;

    //@ public invariant next != null ==> next instanceof JMLEqualsBagEntryNode;

    /** The type of the elements contained in the entries in this list.
     */
    //@ ghost public \TYPE entryElementType;

    //@ public constraint entryElementType == \old(entryElementType);

    //@ public invariant entryElementType <: \type(E);

    /*@ public invariant
      @      val != null && val instanceof JMLEqualsBagEntry
      @      && ((JMLEqualsBagEntry)val).elementType <: entryElementType;
      @  public invariant
      @    (next != null
      @       ==> ((JMLEqualsBagEntryNode<E>)next).entryElementType
      @             <: entryElementType);
      @  public invariant
      @    containsNullElements ==> entryElementType == \type(Object);
      @*/

    /** Whether this list can contain null elements in its bag entries;
     */
    //@ ghost public boolean containsNullElements;

    //@ public constraint containsNullElements == \old(containsNullElements);

    /*@ protected
      @    invariant containsNullElements <==>
      @                ((JMLEqualsBagEntry<E>)val).theElem == null
      @             || (next != null
      @                 && ((JMLEqualsBagEntryNode<E>)next).containsNullElements);
      @*/

    /** Initialize this list to have the given bag entry as its first
     * element followed by the given list.
     * This does not do any cloning.
     *
     * @param entry the JMLEqualsBagEntry<E> to place at the head of this list.
     * @param nxt the JMLEqualsBagEntryNode<E> to make the tail of this list.
     * @see #cons
     */
    /*@  public normal_behavior
      @    requires entry != null;
      @    assignable val, next, elementType, containsNull, owner;
      @    assignable entryElementType, containsNullElements;
      @    ensures val.equals(entry);
      @*/
    /*@    ensures next == nxt;
      @    ensures entryElementType
      @             == (nxt == null ? entry.elementType
      @                 : (nxt.entryElementType <: entry.elementType
      @                    ? entry.elementType
      @                    : ((entry.elementType <: nxt.entryElementType)
      @                       ? nxt.entryElementType
      @                       : \type(NormParameter_))));
      @    ensures containsNullElements
      @             == (((JMLEqualsBagEntry<E>)val).theElem == null
      @                 || (next != null
      @                     && ((JMLEqualsBagEntryNode<E>)next)
      @                         .containsNullElements));
      @*/
    public JMLEqualsBagEntryNode(/*@ non_null @*/ JMLEqualsBagEntry<E> entry,
                                 JMLEqualsBagEntryNode<E> nxt) {
        super(entry, nxt);
        //@ assume elementType == \type(JMLEqualsBagEntry) && !containsNull;
        //@ assert owner == null;
        /*@ set entryElementType
          @      = (nxt == null ? entry.elementType
          @           : (nxt.entryElementType <: entry.elementType
          @              ? entry.elementType
          @              // types aren't totally ordered!
          @              : ((entry.elementType <: nxt.entryElementType)
          @                 ? nxt.entryElementType
          @                 : \type(Object))));
          @ set containsNullElements
          @       = (((JMLEqualsBagEntry<E>)val).theElem == null
          @          || (next != null
          @              && ((JMLEqualsBagEntryNode<E>)next)
          @                  .containsNullElements));
          @*/
    } //@ nowarn Invariant;

    /** Return a JMLEqualsBagEntryNode<F> containing the given entry
     *  followed by the given list.
     *
     * This method handles any necessary cloning for value lists
     * and it handles inserting null elements.
     *
     * @param hd the JMLEqualsBagEntry<F> to place at the head of the result.
     * @param tl the JMLEqualsBagEntryNode<F> to make the tail of the result.
     * @see #JMLEqualsBagEntryNode<F>
     */
    /*@  public normal_behavior
      @    requires hd != null;
      @    ensures \result != null
      @         && \result.headEquals(hd) && \result.next == tl;
      @    ensures \result.equals(new JMLEqualsBagEntryNode<F>(hd, tl));
      @ implies_that
      @    requires hd != null;
      @    ensures tl == null <==> \result.next == null;
      @    ensures \result != null && \result.val instanceof JMLEqualsBagEntry
      @         && \result.entryElementType
      @             == (\result.next == null
      @                 ? ((JMLEqualsBagEntry<F>)\result.val).elementType
      @                 : (((JMLEqualsBagEntryNode<F>)\result.next)
      @                               .entryElementType
      @                        <: ((JMLEqualsBagEntry<F>)\result.val).elementType
      @                    ? ((JMLEqualsBagEntry<F>)\result.val).elementType
      @                    : ((((JMLEqualsBagEntry<F>)\result.val).elementType
      @                          <: ((JMLEqualsBagEntryNode<F>)\result.next)
      @                              .entryElementType)
      @                       ? ((JMLEqualsBagEntryNode<F>)\result.next)
      @                              .entryElementType
      @                       : \type(F))));
      @    ensures \result != null
      @         && \result.containsNullElements
      @             == (((JMLEqualsBagEntry)\result.val).theElem == null
      @                 || (\result.next != null
      @                     && ((JMLEqualsBagEntryNode<F>)\result.next)
      @                         .containsNullElements));
      @*/
    public static <F> /*@ pure @*/ /*@ non_null @*/
        JMLEqualsBagEntryNode<F> cons(/*@ non_null @*/ JMLEqualsBagEntry<F> hd,
                                   JMLEqualsBagEntryNode<F> tl)
    {
        return new JMLEqualsBagEntryNode<F>((JMLEqualsBagEntry<F>) hd.clone(),
                                         tl);
    } //@ nowarn Post;

    /** Return a clone of this object.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result != null
      @    && \result instanceof JMLEqualsBagEntryNode
      @    && ((JMLEqualsBagEntryNode<E>)\result).equals(this);
      @*/
    public /*@ non_null @*/ Object clone() {
        // Recall that cons() handles cloning.
        return cons(val,
                    (next == null
                     ? null
                     : (JMLEqualsBagEntryNode<E>) next.clone()));
    } //@ nowarn Post;

    /** Return a list that is like this list but without the first
     * occurrence of the given bag entry.
     */
    /*@  public normal_behavior
      @    requires !has(entry);
      @    ensures this.equals(\result);
      @ also
      @  public normal_behavior
      @    old int index = indexOf(entry);
      @    requires has(entry);
      @    ensures \result == null <==> \old(int_size() == 1);
      @    ensures \result != null && index == 0
      @        ==> \result.equals(removePrefix(1));
      @    ensures \result != null && index > 0
      @        ==> \result.equals(prefix(index).concat(removePrefix((int)(index+1))));
      @*/
    public JMLEqualsBagEntryNode<E>
        removeBE(/*@ non_null @*/ JMLEqualsBagEntry<E> entry)
    {
        if (entry.equals(val)) {
            if (next == null) {
                return null;
            } else {
                return (JMLEqualsBagEntryNode<E>) next;
            }
        } else {
            JMLEqualsBagEntryNode<E> rest
                = (next == null ? null
                   : ((JMLEqualsBagEntryNode<E>)next).removeBE(entry));
            return new JMLEqualsBagEntryNode<E>((JMLEqualsBagEntry<E>) val,
                                             rest);
        }
    }

}
