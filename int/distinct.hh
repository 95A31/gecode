/*
 *  Main authors:
 *     Christian Schulte <schulte@gecode.org>
 *     Guido Tack <tack@gecode.org>
 *
 *  Contributing authors:
 *     Gabor Szokoli <szokoli@gecode.org>
 *
 *  Copyright:
 *     Christian Schulte, 2002
 *     Guido Tack, 2004
 *     Gabor Szokoli, 2003
 *
 *  Last modified:
 *     $Date$ by $Author$
 *     $Revision$
 *
 *  This file is part of Gecode, the generic constraint
 *  development environment:
 *     http://www.gecode.org
 *
 *  See the file "LICENSE" for information on usage and
 *  redistribution of this file, and for a
 *     DISCLAIMER OF ALL WARRANTIES.
 *
 */

#ifndef __GECODE_INT_DISTINCT_HH__
#define __GECODE_INT_DISTINCT_HH__

#include "int.hh"

#include "int/rel.hh"

/**
 * \namespace Gecode::Int::Distinct
 * \brief %Distinct propagators
 */

namespace Gecode { namespace Int { namespace Distinct {

  /**
   * \brief Naive value distinct propagator
   *
   * Eliminates values of assigned views of type \a View.
   *
   * Requires \code #include "int/distinct.hh" \endcode
   * \ingroup FuncIntProp
   */
  template <class View>
  class Val {
  public:
    /// Post propagator for view array \a x
    static ExecStatus post(Space* home, ViewArray<View>& x);
  };

  /**
   * \brief Implementation of naive value distinct propagator
   *
   * The actual implementation of naive value distinct. If \a shared
   * is true, the propagator takes into account that some views are shared.
   */
  template <class View, bool shared>
  class ValImp : public NaryPropagator<View,PC_INT_VAL> {
    friend class Val<View>;
  protected:
    using NaryPropagator<View,PC_INT_VAL>::x;

    /// Constructor for posting
    ValImp(Space* home, ViewArray<View>& x);
    /// Constructor for cloning \a p
    ValImp(Space* home, bool share, ValImp<View,shared>& p);
  public:
    /// Copy propagator during cloning
    virtual Actor*     copy(Space* home, bool share);
    /// Perform propagation
    virtual ExecStatus propagate(Space* home);
  };

  /**
   * \brief Eliminate singletons by naive value propagation
   *
   * This is actually the propagation algorithm for Distinct::Val.
   * It is available as separate function as it is reused for
   * both bounds-consistent and domain-consistent distinct
   * propagators.
   *
   * If \a complete is true, computes fixpoint, otherwise might not
   * compute fixpoint. This can be helpful when used together with
   * bounds or domain propagation to protect from pathological cases
   * which can be handled more efficiently with bounds propagation.
   *
   * If \a shared is true, takes into account that some views are shared.
   * \relates Gecode::Distinct::Val
   */
  template <class View, bool complete, bool shared>
  ExecStatus prop_val(Space* home, ViewArray<View>&);



  /**
   * \brief Bounds-consistent distinct propagator
   *
   * The propagator uses staging: first it uses naive value-based
   * propagation and only then uses bounds-consistent propagation.
   * Due to using naive value-based propagation, the propagator
   * might actually achieve stronger consistency than just 
   * bounds-consistency.
   *
   * The algorithm is taken from:
   *	A. Lopez-Ortiz, C.-G. Quimper, J. Tromp, and P. van Beek.
   *	A fast and simple algorithm for bounds consistency of the
   *	alldifferent constraint. IJCAI-2003.
   *
   * This implementation uses the code that is provided by
   * Peter Van Beek:
   *   http://ai.uwaterloo.ca/~vanbeek/software/software.html
   * The code (originally by John Tromp) here has only been slightly modified
   * to fit %Gecode (taking idempotent/non-idempotent propagation into account)
   * and uses a more efficient layout of datastructures (keeping the number
   * of different arrays small).
   *
   * The Bnd class only posts propagators, the actual implementation
   * is BndImp which handles shared views.
   *
   * Requires \code #include "int/distinct.hh" \endcode
   * \ingroup FuncIntProp
   */
  template <class View>
  class Bnd {
  public:
    /// Post propagator for view array \a x
    static ExecStatus post(Space* home, ViewArray<View>& x);
  };

  /**
   * \brief Implementation of bounds-consistent distinct propagator
   *
   * The actual implementation of bounds-consistent distinct. If \a shared
   * is true, the propagator takes into account that some views are shared.
   */
  template <class View, bool shared>
  class BndImp : public Propagator {
    friend class Bnd<View>;
  protected:
    /// Views on which to perform bounds-propagation
    ViewArray<View> x; 
    /// Views on which to perform value-propagation (subset of \c x) 
    ViewArray<View> y;
    /// Constructor for posting
    BndImp(Space* home, ViewArray<View>& x);
    /// Constructor for cloning \a p
    BndImp(Space* home, bool share, BndImp<View,shared>& p);
  public:
    /// Perform propagation
    virtual ExecStatus propagate(Space* home);
    /**
     * \brief Cost function
     *
     * If in stage for naive value propagation, the cost is dynamic
     * PC_LINEAR_LO. Otherwise it is dynamic PC_LINEAR_HI.
     */
    virtual PropCost cost(void) const;
    /// Copy propagator during cloning
    virtual Actor* copy(Space* home, bool share);
    /// Destructor
    virtual ~BndImp(void);
  };

  /**
   * \brief Perform bounds-consistent distinct propagation
   *
   * This is actually the propagation algorithm for Distinct::BndImp.
   * It is available as separate function as it is reused for
   * both bounds-consistent and domain-consistent distinct
   * propagators.
   *
   * If \a shared is true, propagation takes into account that 
   * some views are shared.
   */
  template <class View, bool shared>
  ExecStatus prop_bnd(Space* home, ViewArray<View>& x);



  /**
   * \brief Domain-consistent distinct propagator
   *
   * The propagator uses staging: first it uses naive value-based
   * propagation and only then uses domain-consistent propagation.
   *
   * The algorithm is taken from:
   *    Jean-Charles R�gin, A filtering algorithm for constraints
   *    of difference in CSPs, Proceedings of the Twelfth National
   *    Conference on Artificial Intelligence, pages 362--367.
   *    Seattle, WA, USA, 1994.
   *
   * Requires \code #include "int/distinct.hh" \endcode
   * \ingroup FuncIntProp
   */
  template <class View>
  class Dom : public NaryPropagator<View,PC_INT_DOM> {
  protected:
    using NaryPropagator<View,PC_INT_DOM>::x;

    /// View-value graph for propagation
    class ViewValGraph;
    /// Propagation is performed on a view-value graph (used as cache)
    ViewValGraph* vvg;
    /// Constructor for cloning \a p
    Dom(Space* home, bool share, Dom<View>& p);
    /// Constructor for posting
    Dom(Space* home, ViewArray<View>& x);
  public:
    /// Perform propagation
    virtual ExecStatus propagate(Space* home);
    /**
     * \brief Cost function
     *
     * If in stage for naive value propagation, the cost is dynamic
     * PC_LINEAR_LO. Otherwise it is dynamic PC_CUBIC_LO.
     */
    virtual PropCost cost(void) const;
    /// Copy propagator during cloning
    virtual Actor* copy(Space* home, bool share);
    /// Destructor
    virtual ~Dom(void);
    /// Flush view-value graph
    virtual void flush(void);
    /// Returns size of view-value graph
    virtual size_t size(void) const;
    /// Post propagator for views \a x
    static  ExecStatus post(Space* home, ViewArray<View>& x);
  };

}}}

#include "int/distinct/val.icc"
#include "int/distinct/bnd.icc"
#include "int/distinct/dom.icc"

#endif

// STATISTICS: int-prop

