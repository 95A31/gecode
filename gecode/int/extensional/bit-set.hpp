/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */
/*
 *  Main authors:
 *     Linnea Ingmar <linnea.ingmar@hotmail.com>
 *
 *  Contributing authors:
 *     Christian Schulte <schulte@gecode.org>
 *
 *  Copyright:
 *     Linnea Ingmar, 2017
 *     Christian Schulte, 2017
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

namespace Gecode { namespace Int { namespace Extensional {

  template<class IndexType>
  forceinline
  BitSet<IndexType>::BitSet(Space& home, unsigned int n)
    : _limit(static_cast<IndexType>(n)), 
      index(home.alloc<IndexType>(n)),
      bits(home.alloc<BitSetData>(n)) {
    // Set all bits in all words (including the last)
    for (IndexType i=_limit; i--; ) {
      bits[i].init(true);
      index[i] = i;
    }
  }

  template<class IndexType>
  template<class OldIndexType>
  forceinline
  BitSet<IndexType>::BitSet(Space& home,
                            const BitSet<OldIndexType>& bs)
    : _limit(static_cast<IndexType>(bs._limit)),
      index(home.alloc<IndexType>(_limit)),
      bits(home.alloc<BitSetData>(_limit)) {
    assert(_limit > 0U);
    for (IndexType i = _limit; i--; ) {
      bits[i] = bs.bits[i];
      index[i] = static_cast<IndexType>(bs.index[i]);
    }
  }
  
  template<class IndexType>
  forceinline
  BitSet<IndexType>::BitSet(Space&, const TinyBitSet<1U>&) {
    GECODE_NEVER;
  }
  template<class IndexType>
  forceinline
  BitSet<IndexType>::BitSet(Space&, const TinyBitSet<2U>&) {
    GECODE_NEVER;
  }
  template<class IndexType>
  forceinline
  BitSet<IndexType>::BitSet(Space&, const TinyBitSet<3U>&) {
    GECODE_NEVER;
  }
  template<class IndexType>
  forceinline
  BitSet<IndexType>::BitSet(Space&, const TinyBitSet<4U>&) {
    GECODE_NEVER;
  }

  template<class IndexType>
  forceinline void
  BitSet<IndexType>::replace_and_decrease(IndexType i, BitSetData w) {
    assert(_limit > 0U);
    BitSetData w_i = bits[i];
    if (w != w_i) {
      bits[i] = w;
      if (w.none()) {
        assert(bits[i].none());
        bits[i] = bits[_limit-1];
        index[i] = index[_limit-1];
        _limit--;
      }
    }
  }

  template<class IndexType>
  forceinline void
  BitSet<IndexType>::clear_mask(BitSetData* mask) const {
    assert(_limit > 0U);
    for (IndexType i = _limit; i--; ) {
      mask[i].init(false);
      assert(mask[i].none());
    }
  }
  
  template<class IndexType>
  forceinline void
  BitSet<IndexType>::add_to_mask(const BitSetData* b, BitSetData* mask) const {
    assert(_limit > 0U);
    for (IndexType i = _limit; i--; )
      mask[i] = BitSetData::o(mask[i],b[index[i]]);
  }

  template<class IndexType>
  template<bool sparse>
  forceinline void
  BitSet<IndexType>::intersect_with_mask(const BitSetData* mask) {
    assert(_limit > 0U);
    if (sparse) {
      for (IndexType i = _limit; i--; ) {
        assert(!bits[i].none());
        BitSetData w_i = bits[i];
        BitSetData w_a = BitSetData::a(w_i, mask[index[i]]);
        replace_and_decrease(i,w_a);
        assert(i == _limit || !bits[i].none());
      }
    } else { // The same except different indexing in mask
      for (IndexType i = _limit; i--; ) {
        assert(!bits[i].none());
        BitSetData w_i = bits[i];
        BitSetData w_a = BitSetData::a(w_i, mask[i]);
        replace_and_decrease(i,w_a);
        assert(i == _limit || !bits[i].none());
      }
    }
  }
  
  template<class IndexType>
  forceinline void
  BitSet<IndexType>::intersect_with_masks(const BitSetData* a,
                                          const BitSetData* b) {
    assert(_limit > 0U);
    for (IndexType i = _limit; i--; ) {
      assert(!bits[i].none());
      BitSetData w_i = bits[i];
      IndexType offset = index[i];
      BitSetData w_o = BitSetData::o(a[offset], b[offset]);
      BitSetData w_a = BitSetData::a(w_i,w_o);
      replace_and_decrease(i,w_a);
      assert(i == _limit || !bits[i].none());
    }
  }
  
  template<class IndexType>
  forceinline void
  BitSet<IndexType>::nand_with_mask(const BitSetData* b) {
    assert(_limit > 0U);
    for (IndexType i = _limit; i--; ) {
      assert(!bits[i].none());
      BitSetData w = BitSetData::a(bits[i],~(b[index[i]]));
      replace_and_decrease(i,w);
      assert(i == _limit || !bits[i].none());
    }
  }

  template<class IndexType>
  forceinline bool
  BitSet<IndexType>::intersects(const BitSetData* b) const {
    for (IndexType i = _limit; i--; )
      if (!BitSetData::a(bits[i],b[index[i]]).none())
        return true;
    return false;
  }
  
  
  template<class IndexType>
  forceinline unsigned int
  BitSet<IndexType>::limit(void) const {
    return static_cast<unsigned int>(_limit);
  }
  
  template<class IndexType>
  forceinline bool
  BitSet<IndexType>::empty(void) const {
    return _limit == 0U;
  }
  
  template<class IndexType>
  forceinline unsigned int
  BitSet<IndexType>::words(void) const {
    return static_cast<unsigned int>(_limit);
  }

  template<class IndexType>
  forceinline unsigned int
  BitSet<IndexType>::size(void) const {
    return words();
  }
      
  template<class IndexType>
  forceinline unsigned int
  BitSet<IndexType>::width(void) const {
    assert(!empty());
    IndexType width = index[0];
    for (IndexType i = _limit; i--; ) {
      width = std::max(width,index[i]);
    }
    assert(static_cast<unsigned int>(width+1U) >= words());
    return static_cast<unsigned int>(width+1U);
  }

}}}

// STATISTICS: int-prop
