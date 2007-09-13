/*
 *  Main authors:
 *     Guido Tack <tack@gecode.org>
 *     Christian Schulte <schulte@gecode.org>
 *
 *  Copyright:
 *     Guido Tack, 2005
 *     Christian Schulte, 2005
 *
 *  Last modified:
 *     $Date$ by $Author$
 *     $Revision$
 *
 *  This file is part of Gecode, the generic constraint
 *  development environment:
 *     http://www.gecode.org
 *
 *  Permission is hereby granted, free of charge, to any person obtaining
 *  a copy of this software and associated documentation files (the
 *  "Software"), to deal in the Software without restriction, including
 *  without limitation the rights to use, copy, modify, merge, publish,
 *  distribute, sublicense, and/or sell copies of the Software, and to
 *  permit persons to whom the Software is furnished to do so, subject to
 *  the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 *  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 *  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 *  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

#ifndef __GECODE_TEST_CPLTSET_HH__
#define __GECODE_TEST_CPLTSET_HH__

#include "gecode/cpltset.hh"
#include "test/test.hh"
#include "test/set.hh"
#include "test/int.hh"

using namespace Test;
using namespace Gecode;
using namespace Set;
using namespace CpltSet;

class CpltSetTest : public Base {
private:
  int     arity;
  IntSet  lub;
  bool    reified;
  int    withInt;
  int ivs;
  int ics;

  void removeFromLub(int, CpltSetVar&, int, const IntSet&);
  void addToGlb(int, CpltSetVar&, int, const IntSet&);
  SetAssignment* make_assignment(void);
public:
  CpltSetTest(const std::string& s, int a, const IntSet& d, bool r=false,
              int w=0, int mn=10000, int mc=1000) 
    : Base("CpltSet::"+s), arity(a), lub(d), reified(r), withInt(w), 
      ivs(mn), ics(mc)  {
    CpltSet::manager.dispose();
    CpltSet::manager.init(mn, mc);
  }

  /// Check for solution
  virtual bool solution(const SetAssignment&) const = 0;
  /// Post propagator
  virtual void post(Space* home, CpltSetVarArray& x, IntVarArray& y) = 0;
  /// Post reified propagator
  virtual void post(Space* home, CpltSetVarArray& x, IntVarArray& y,
                    BoolVar b) {}
  /// Perform test
  virtual bool run(const Options& opt);

  template <class I>
  int iter2int(I& r, int u) const{
    if (!r()) {
      return 0;
    }
    int v = 0;
    // compute the bit representation of the assignment 
    // and convert it to the corresponding integer
    while(r()) {
      v  |= (1 << r.val()); // due to reversed lex ordering
      ++r;
    }
    return v;
  }
  
  /// Provide manager access
  int varsize(void) { return ivs; }
  int cachesize(void) { return ics; }

};

#endif

// STATISTICS: test-cpltset
