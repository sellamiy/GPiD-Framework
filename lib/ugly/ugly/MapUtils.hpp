#ifndef LIB_UGLY__MAP_UTILS_HPP
#define LIB_UGLY__MAP_UTILS_HPP

#include <map>

namespace ugly {

    template <typename K, typename V>
    static inline bool mapHasValue(const std::map<K, V>& m, const V& v) {
        for (auto p : m)
            if (p.second == v)
                return true;
        return false;
    }

}

#endif
