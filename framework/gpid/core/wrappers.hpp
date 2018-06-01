/**
 * \file gpid/core/wrappers.hpp
 * \brief GPiD-Framework Core wrappers.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__WRAPPERS_HPP
#define GPID_FRAMEWORK__CORE__WRAPPERS_HPP

#include <map>
#include <starray/starray.hpp>

namespace gpid {

    /** \brief Class for mapping indices to literals. */
    template<class LiteralT>
    struct LiteralMapper {
        typedef uint32_t index_t;

        inline void map(index_t idx, LiteralT* l);
        inline LiteralT& get(index_t idx);

        inline uint32_t size();
    private:
        std::map<index_t, LiteralT*> _mapping;
    };

    template<class LiteralT> class LiteralHypothesisPrinter;

    template<class LiteralT>
    class LiteralHypothesis {
    public:
        typedef uint32_t index_t;
    private:
        starray::SequentialActivableArray _array;
        std::map<uint32_t, std::vector<index_t>> _lmapping;
    public:
        LiteralHypothesis(uint32_t size) : _array(size)
        { for (uint32_t i = 0; i < size; ++i) _array.deactivate(i); }

        inline void addLiteral(index_t lidx, uint32_t lkey);
        inline void removeLiterals(uint32_t lkey);

        typedef typename starray::SequentialActivableArray::iterator iterator;
        typedef typename starray::SequentialActivableArray::const_iterator const_iterator;
        inline       iterator begin()  { return _array.begin();  }
        inline       iterator end()    { return _array.end();    }
        inline const_iterator cbegin() { return _array.cbegin(); }
        inline const_iterator cend()   { return _array.cend();   }

        friend LiteralHypothesisPrinter<LiteralT>;
    };

    template<class LiteralT> class LiteralHypothesisPrinter;
    template<class LiteralT> std::ostream& operator<<
    (std::ostream& os, const LiteralHypothesisPrinter<LiteralT>& hlp);

    template<class LiteralT>
    class LiteralHypothesisPrinter {
        LiteralHypothesis<LiteralT>& hypothesis;
        LiteralMapper<LiteralT>& mapper;
        bool negate;
    public:
        LiteralHypothesisPrinter
        (LiteralHypothesis<LiteralT>& lh, LiteralMapper<LiteralT>& mp, bool neg=true)
            : hypothesis(lh), mapper(mp), negate(neg) {}
        LiteralHypothesisPrinter(const LiteralHypothesisPrinter<LiteralT>& o)
            : hypothesis(o.hypothesis), mapper(o.mapper), negate(o.negate) {}

        friend std::ostream& operator<< <LiteralT>
        (std::ostream& os, const LiteralHypothesisPrinter<LiteralT>& hlp);
    };

    /* *** Implementations *** */

    template<class LiteralT>
    inline void LiteralMapper<LiteralT>::map(index_t idx, LiteralT* l) {
        _mapping[idx] = l;
    }

    template<class LiteralT>
    inline LiteralT& LiteralMapper<LiteralT>::get(index_t idx) {
        return *_mapping[idx];
    }

    template<class LiteralT>
    inline uint32_t LiteralMapper<LiteralT>::size() {
        return _mapping.size();
    }

    template<class LiteralT>
    inline void LiteralHypothesis<LiteralT>::addLiteral(index_t lidx, uint32_t lkey) {
        _array.activate(lidx);
        _lmapping[lkey].push_back(lidx);
    }

    template<class LiteralT>
    inline void LiteralHypothesis<LiteralT>::removeLiterals(uint32_t lkey) {
        for (index_t lidx : _lmapping[lkey]) {
            _array.deactivate(lidx);
        }
        _lmapping[lkey].clear();
    }

    template<class LiteralT>
    inline const LiteralHypothesisPrinter<LiteralT> implicate
    (LiteralHypothesis<LiteralT>& h, LiteralMapper<LiteralT>& mp)
    { return LiteralHypothesisPrinter<LiteralT>(h, mp, true); }

    template<class LiteralT>
    inline const LiteralHypothesisPrinter<LiteralT> hypothesis
    (LiteralHypothesis<LiteralT>& h, LiteralMapper<LiteralT>& mp)
    { return LiteralHypothesisPrinter<LiteralT>(h, mp, false); }

    template<class Printable>
    inline void print_item(Printable& p)
    { std::cout << "> " << p << std::endl; }

}

#endif
