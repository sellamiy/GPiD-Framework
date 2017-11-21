#ifndef LIB_STARRAY__STATIC_ACTIVABLE_ARRAY_HPP
#define LIB_STARRAY__STATIC_ACTIVABLE_ARRAY_HPP

#include <cinttypes>

namespace starray {

    /**
     * @brief Array of activated elements.
     *
     * This class represents an array of elements that may or may not
     * be activated. It allows access to elements in O(1) and keeps a
     * linked list structure of the active elements to allow one to 
     * iterate over the active elements in O(|{active elements}|).
     */
    class StaticActivableArray
    {
    public:
        /**
         * @brief Allocates an ActivableArray.
         *
         * Allocates an ActivableArray and initialises the
         * internal data structure. All the boxes starts active.
         *
         * @param size - Size of ActivableArray to allocate.
         */
        StaticActivableArray(uint32_t size);
        /**
         * @brief Frees the internal memory of the ActivableArray.
         */
        ~StaticActivableArray();
        /**
         * @brief Activates a box of the ActivableArray.
         *
         * (Does nothing if the box is already active.)
         *
         * @param i - Index of the box to activate.
         * Must exist in the allocated array.
         * @note Complexity: O(1).
         */
        void activate(uint32_t i);
        /**
         * @brief Deactivates a box of the ActivableArray.
         *
         * (Does nothing if the box is already inactive.)
         *
         * @param i - Index of the box to deactivate.
         * Must exist in the allocated array.
         * @note Complexity: O(1).
         */
        void deactivate(uint32_t i);
        /**
         * @brief Check if a box of the ActivableArray is active or not.
         *
         * @param i - Index of the box to check.
         * Must exist in the allocated array.
         * @return a positive value if the box is active, 0 otherwise.
         * In a structural point of view, it returns the value of the
         * corresponding aa_elt element.
         * @note Complexity: O(1).
         */
        inline uint8_t is_active(uint32_t i) {
            // assert(i < total_size);
            // assert(tab[i].value <= 1);
            return (int)tab[i].value;
        }
        // TODO: Add tests for this method!
        /** @warning Untested. */
        inline uint32_t get_maximal_size()
        { return total_size; }
        /**
         * @brief Get the active size of the ActivableArray.
         *
         * I.e.: the number of active elements inside.
         *
         * @return the number of active elements in the ActivableArray.
         * @note Complexity: O(1).
         */
        inline uint32_t get_activated_size()
        { return activated_size; }

        /**
         * @brief Check if the ActivableArray has another active element.
         *
         * This is an ad-hoc iterator method.
         * @return 0 if there are no other active element, a positive value
         * otherwise.
         * @note Complexity: O(1).
         */
        inline uint8_t has_next()
        { return (uint8_t)(list_curr->next != list_last.index); }
        /**
         * @brief Get the ActivableArray next active element.
         *
         * This is an ad-hoc iterator method. It returns the following active
         * element in the list and then advance to this element.
         * The boxes are not necessarily
         * delivered in the index (positive integer) natural order.
         * @return the index of the next active box of the ActivableArray.
         * @warning if has_next has returned 0, a call to this method
         * will result in an illegal memory access.
         * @note Complexity: O(1).
         */
        inline uint32_t get_next() {
            list_curr = &(tab[list_curr->next]);
            return list_curr->index;
        }
        // TODO: Add tests for these two methods!
        /** @warning Untested. */
        inline uint32_t get_first() { return tab[list_first.next].index; }
        /** @warning Untested. */
        inline uint32_t get_last() { return tab[list_last.prev].index; }
        /**
         * @brief Reset the ActivableArray iterator.
         *
         * This is an ad-hoc iterator method. Reset the iterator
         * to the first element of the list.
         * @note Complexity: O(1).
         */
        inline void reset_iterator()
        { list_curr = &list_first; }

        inline void set_it_pos(uint32_t index) {
            // assert(is_active(index));
            list_curr = &(tab[index]);
        }
    private:
        /** @brief Element representation for an ActivableArray box. */
        struct aa_elt {
            /** @brief Value of the box. Positive only if the box is activated */
            uint8_t value;
            /** @brief Index of the box in the array. */
            uint32_t index;
            /** @brief Previous active element. */
            uint32_t prev;
            /** @brief Next active element. */
            uint32_t next;
        };
        typedef aa_elt aa_elt_t;

        /** @brief Maximal size of the ActivableArray. */
        uint32_t total_size;
        /** @brief Number of active elements in the ActivableArray. */
        uint32_t activated_size;
        /** @brief Internal array data structure. */
        aa_elt_t *tab;
        /** @brief Abstract element -1 of the internal Array.
         *
         * Used to ensure the correctness of the list linkage. */
        aa_elt_t list_first;
        /** @brief Position of the ad-hoc iterator. */
        aa_elt_t *list_curr;
        /** @brief Abstract element total_size of the internal Array.
         *
         * Used to ensure the correctness of the list linkage. */
        aa_elt_t list_last;
    };

};
#endif
