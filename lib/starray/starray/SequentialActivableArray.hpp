/**
 * \file starray/SequentialActivableArray.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef LIB_STARRAY__SEQUENTIAL_ACTIVABLE_ARRAY_HPP
#define LIB_STARRAY__SEQUENTIAL_ACTIVABLE_ARRAY_HPP

#include <cinttypes>
#include <snlog/snlog.hpp>

namespace starray {

    /**
     * \brief Array of activable elements with fixed order.
     *
     * The elements of the array may or may not be activated.
     * Activated or not, elements position do not change in the array.
     *
     * Elements may be either Active, Paused or Inactive.
     * Active and Paused elements are browsed by the iterator.
     * Inactive elements are not.
     */
    class SequentialActivableArray
    {
    private:
        enum aa_elt_st { ACTIVE, PAUSED, INACTIVE };
        struct aa_elt {
            aa_elt_st status;
            uint32_t index;
            uint32_t value;
        };
        typedef aa_elt aa_elt_t;

        uint32_t total_size;
        uint32_t active_size;
        aa_elt_t *tab;
    public:
        /** \brief Allocates an ActivableArray. */
        SequentialActivableArray(uint32_t size);
        ~SequentialActivableArray();

        /** \brief SequentialActivableArray elements iterator. */
        template <typename Type>
        class SeqAAIterator {
            aa_elt_t* tptr;
            uint32_t pos;
            bool ooa;
        public:
            SeqAAIterator(aa_elt_t* tab, uint32_t pos, uint32_t ooa_chk, bool ooa=false)
                : tptr(tab), pos(pos), ooa(ooa || pos == ooa_chk) {}
            inline bool operator!=(const SeqAAIterator<Type>& rIt) const
            { return ooa != rIt.ooa || (!ooa && (tptr != rIt.tptr || pos != rIt.pos)); }
            SeqAAIterator& operator++();
            inline       Type operator*()       { return tptr[pos].index; }
            inline const Type operator*() const { return tptr[pos].index; }
        };
        typedef SeqAAIterator<uint32_t> iterator;

        inline iterator begin() { return iterator(tab, get_last(), total_size); }
        inline iterator end()   { return iterator(tab, 0, total_size, true); }
        typedef SeqAAIterator<const uint32_t> const_iterator;
        inline const_iterator cbegin() { return const_iterator(tab, get_last(), total_size); }
        inline const_iterator cend()   { return const_iterator(tab, 0, total_size, true); }

        /** \brief Activate an element of the array. */
        void activate(uint32_t i);
        /** \brief Pause an element of the array. */
        void pause(uint32_t i);
        /** \brief Deactivate an element of the array. */
        void deactivate(uint32_t i);

        inline bool is_active(uint32_t i)
        { return tab[i].status == aa_elt_st::ACTIVE; }
        inline bool is_paused(uint32_t i)
        { return tab[i].status == aa_elt_st::PAUSED; }
        inline bool is_inactive(uint32_t i)
        { return tab[i].status == aa_elt_st::INACTIVE; }

        /** \brief Get the number of active elements in the array. */
        inline uint32_t get_activated_size() { return active_size; }
        /** \brief Get the maximal number of elements in the array. */
        inline uint32_t get_maximal_size()   { return total_size ; }

        /**
         * \brief Get the first downward non inactive element.
         * \param src starting position.
         * \return The first non inactive element of the array between
         *         src and the first element, in this order, if such an element
         *         exists.
         * \return src if the array does not contain any non inactive element
         *         in [0, src[.
         */
        uint32_t get_downward(uint32_t src);
        /**
         * \brief Get the first upward non inactive element.
         * \param src starting position.
         * \return The first non inactive element of the array between
         *         src and the last element, in this order, if such an element
         *         exists.
         * \return src if the array does not contain any non inactive element
         *         in ]src, last].
         */
        uint32_t get_upward(uint32_t src);

        /** \brief Get the last non inactive element in the array. */
        inline uint32_t get_last()  { return get_downward(total_size); }
        /** \brief Get the first non inactive element in the array. */
        inline uint32_t get_first() { return get_upward(0); }

        /** \brief Set the value of an element in the array. */
        inline void set(uint32_t i, uint32_t v) { tab[i].value = v; }
        /** \brief Get the value of an element in the array. */
        inline uint32_t get(uint32_t i)         { return tab[i].value; }
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
