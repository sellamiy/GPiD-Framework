/**
 * \file ugly/BeurkTables.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef LIB_UGLY__BEURK_TABLES_HPP
#define LIB_UGLY__BEURK_TABLES_HPP

#include <set>

namespace ugly {

    template<class O, class InsertionRefuser, class InsertionCleaner>
    class BeurkTable {
        O* bdata;
        unsigned int msize;

        std::set<unsigned int> freelocs;
        std::set<unsigned int> usedlocs;

        InsertionRefuser refuser;
        InsertionCleaner cleaner;

        inline void remove(unsigned int loc) {
            usedlocs.erase(loc);
            freelocs.insert(loc);
        }
    public:
        BeurkTable(unsigned int initial_size=1) {
            bdata = (O*)realloc(NULL, initial_size*sizeof(O));
            msize = initial_size;
            for (unsigned int i=0; i < initial_size; i++) freelocs.insert(i);
        }

        template<class ... InsertionInitializerClasses>
        BeurkTable(InsertionInitializerClasses& ... iie)
            : refuser(iie...), cleaner(iie...)
        {
            unsigned int initial_size = 1;
            bdata = (O*)realloc(NULL, initial_size*sizeof(O));
            msize = initial_size;
            for (unsigned int i=0; i < initial_size; i++) freelocs.insert(i);
        }

        inline bool free_location(unsigned int loc) const {
            return freelocs.find(loc) != freelocs.end();
        }
        inline bool used_location(unsigned int loc) const {
            return usedlocs.find(loc) != usedlocs.end();
        }

        inline unsigned int memorysize() const {
            return msize;
        }

        inline unsigned int size() const {
            return usedlocs.size();
        }

        inline void insert(O elem) {
            if (freelocs.empty()) {
                bdata = (O*)realloc(bdata, 2*msize*sizeof(O));
                for (unsigned int i=msize; i < 2*msize; i++) freelocs.insert(i);
                msize *= 2;
            }
            unsigned int loc = *(freelocs.begin());
            freelocs.erase(loc);
            new (&(bdata[loc])) O(elem);
            usedlocs.insert(loc);
        }

        inline bool dry_insert_refuse(O elem) {
            for (unsigned int loc : usedlocs)
                if (refuser(elem, bdata[loc])) return false;
            return true;
        }

        inline void insert_refuse(O elem) {
            for (unsigned int loc : usedlocs)
                if (refuser(elem, bdata[loc])) return;
            insert(elem);
        }

        inline void insert_clean(O elem) {
        beurklabel:
            for (unsigned int loc : usedlocs)
                if (cleaner(elem, bdata[loc])) { remove(loc); goto beurklabel; }
            insert(elem);
        }

        inline void insert_refuse_clean(O elem) {
        beurklabel:
            for (unsigned int loc : usedlocs) {
                if (refuser(elem, bdata[loc])) return;
                if (cleaner(elem, bdata[loc])) { remove(loc); goto beurklabel; }
            }
            insert(elem);
        }

        template <typename Type>
        class BeurkTableIterator {
            const O* bdata;
            std::set<unsigned int>& source;
            std::set<unsigned int>::iterator rpos;
        public:
            BeurkTableIterator(const O* bdata, std::set<unsigned int>& source,
                               std::set<unsigned int>::iterator rpos)
                : bdata(bdata), source(source), rpos(rpos) {}
            inline bool operator!=(const BeurkTableIterator<Type>& rIt) const
            { return rpos != rIt.rpos /* || source != rIt.source */ ; }
            inline BeurkTableIterator& operator++() { ++rpos; return *this; }
            inline       Type operator*()       { return bdata[*rpos]; }
            inline const Type operator*() const { return bdata[*rpos]; }
        };

        typedef BeurkTableIterator<O> iterator;
        typedef BeurkTableIterator<const O> const_iterator;
        inline iterator begin() { return iterator(bdata, usedlocs, usedlocs.begin()); }
        inline iterator end()   { return iterator(bdata, usedlocs, usedlocs.end()); }
        inline const_iterator cbegin() { return const_iterator(bdata, usedlocs, usedlocs.cbegin()); }
        inline const_iterator cend()   { return const_iterator(bdata, usedlocs, usedlocs.cend()); }

    };

}

#endif
