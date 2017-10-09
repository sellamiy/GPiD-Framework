#ifndef _SEQUENTIAL_ACTIVABLE_ARRAY_HPP_
#define _SEQUENTIAL_ACTIVABLE_ARRAY_HPP_

#include <cinttypes>

namespace starray {

    class SequentialActivableArray
    {
    private:
        enum aa_elt_st { ACTIVE, PAUSED, INACTIVE };
        struct aa_elt {
            aa_elt_st status;
            uint32_t index;
        };
        typedef aa_elt aa_elt_t;

        uint32_t total_size;
        uint32_t active_size;
        aa_elt_t *tab;
    public:
        SequentialActivableArray(uint32_t size);
        ~SequentialActivableArray();

        template <typename Type>
        class SeqAAIterator {
            aa_elt_t* tptr;
            uint32_t pos;
            bool ooa;
        public:
            SeqAAIterator(aa_elt_t* tab, uint32_t pos, bool ooa=false)
                : tptr(tab), pos(pos), ooa(ooa) {}
            inline bool operator!=(const SeqAAIterator<Type>& rIt) const
            { return ooa != rIt.ooa && (tptr != rIt.tptr || pos != rIt.pos); }
            SeqAAIterator& operator++();
            inline       Type operator*()       { return tptr[pos].index; }
            inline const Type operator*() const { return tptr[pos].index; }
        };
        typedef SeqAAIterator<uint32_t> iterator;
        inline iterator begin() { return iterator(tab, get_last()); }
        inline iterator end()   { return iterator(tab, 0, true); }
        typedef SeqAAIterator<const uint32_t> const_iterator;
        inline const_iterator cbegin() { return const_iterator(tab, get_last()); }
        inline const_iterator cend()   { return const_iterator(tab, 0, true); }

        void activate(uint32_t i);
        void pause(uint32_t i);
        void deactivate(uint32_t i);

        inline bool is_active(uint32_t i)
        { return tab[i].status == aa_elt_st::ACTIVE; }
        inline bool is_paused(uint32_t i)
        { return tab[i].status == aa_elt_st::PAUSED; }
        inline bool is_inactive(uint32_t i)
        { return tab[i].status == aa_elt_st::INACTIVE; }

        inline uint32_t get_activated_size() { return active_size; }
        inline uint32_t get_maximal_size()   { return total_size ; }

        uint32_t get_last();
        uint32_t get_first();
    };

    template<typename Type> inline SequentialActivableArray::SeqAAIterator<Type>&
    SequentialActivableArray::SeqAAIterator<Type>::operator++() {
        do {
            if (pos == 0) {
                ooa = true;
                break;
            }
            --pos;
        }
        while(tptr[pos].status == aa_elt_st::INACTIVE);
        return *this;
    }

};
#endif
