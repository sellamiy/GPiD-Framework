#ifndef _UGLY_SET_OF_SETS_HPP_
#define _UGLY_SET_OF_SETS_HPP_

#include <set>
#include <snlog/snlog.hpp>

namespace ugly {

    template<typename Type, typename SetType>
    class SetOfSets {
        std::set<std::set<Type> > data;
    public:
        void addSet(SetType& s);
        bool subsets(SetType& s);
    };

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
