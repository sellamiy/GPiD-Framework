#ifndef _MINISAT_WRAPPERS_HPP
#define _MINISAT_WRAPPERS_HPP

#include <minisat/core/SolverTypes.h>

namespace gpid {
    template<class T>
    struct MinisatVecWrapper {

        template<typename Type>
        class MinisatVecIterator {
            Minisat::vec<T>& data;
            int pos;
        public:
            MinisatVecIterator(Minisat::vec<T>& data, int pos) : data(data), pos(pos) {}
            inline bool operator!=(const MinisatVecIterator<Type>& rIt) const
            { return pos != rIt.pos; }
            MinisatVecIterator& operator++()    { pos++; return *this; }
            inline       Type operator*()       { return data[pos]; }
            inline const Type operator*() const { return data[pos]; }
        };
        typedef MinisatVecIterator<Minisat::Lit> iterator;
        typedef MinisatVecIterator<const Minisat::Lit> const_iterator;
        
        Minisat::vec<T>& data;

        inline MinisatVecWrapper(Minisat::vec<T>& d) : data(d) {}
        inline bool contains(T& t) const {
            for (int i = 0; i < data.size(); i++)
                if (data[i] == t) return true;
            return false;
        }

        inline iterator begin() { return iterator(data, 0); }
        inline iterator end()   { return iterator(data, data.size()); }
        inline const_iterator cbegin() { return const_iterator(data, 0); }
        inline const_iterator cend()   { return const_iterator(data, data.size()); }
    };
}

#endif
