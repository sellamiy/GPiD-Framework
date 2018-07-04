/**
 * \file ugly/SetOfSets.hpp
 */
#ifndef LIB_UGLY__SET_OF_SETS_HPP
#define LIB_UGLY__SET_OF_SETS_HPP

#include <set>

namespace ugly {

    /** \brief An ugly implementation for grouping sets in a set. */
    template<typename Type, typename SetType>
    class SetOfSets {
        std::set<std::set<Type> > data;
    public:
        /** \brief Add a set to the set of sets by full copy. */
        void addSet(SetType& s);
        /** \brief Does this set subsets another. \see ugly::isSubset */
        bool subsets(SetType& s);
    };

    /**
     * \brief An ugly and naive implementation of the subset test.
     * \warning Browses every single element of every single set.
     * \param s Requested containing set.
     * \param t Requested contained set.
     * \return true iff s is a subset of t.
     */
    template<typename Type, typename SetType>
    inline bool isSubset(const std::set<Type>& s, const SetType& t) {
        for (Type d : s) {
            if (!t.contains(d)) return false;
        }
        return true;
    }

    template<typename Type, typename SetType>
    inline void SetOfSets<Type, SetType>::addSet(SetType& s) {
        std::set<Type> t;
        for (Type d : s) t.insert(d);
        data.insert(t);
    }
    template<typename Type, typename SetType>
    inline bool SetOfSets<Type, SetType>::subsets(SetType& s) {
        for (const std::set<Type>& l : data) {
            if (isSubset<Type, SetType>(l, s)) return true;
        }
        return false;
    }

};
#endif
