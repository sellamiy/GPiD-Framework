/**
 * \file gpid/utils/stdutils.hpp
 * \brief Misc. utils for standard library
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__UTILS__STDUTILS_HPP
#define GPID_FRAMEWORK__UTILS__STDUTILS_HPP

#include <map>
#include <set>

namespace gmisc {

    /** Check if a standard set contains a given key. */
    template<class T>
    inline bool inset(const std::set<T>& s, const T& val)
    { return s.find(val) != s.end(); }

    /** Check if a standard set does not contain a given key. */
    template<class T>
    inline bool ninset(const std::set<T>& s, const T& val)
    { return s.find(val) == s.end(); }

    /** Check if a standard map contains a given key. */
    template<class Key, class T>
    inline bool inmap(const std::map<Key, T>& m, const Key& key)
    { return m.find(key) != m.end(); }

    /** Check if a standard map does not contain a given key. */
    template<class Key, class T>
    inline bool ninmap(const std::map<Key, T>& m, const Key& key)
    { return m.find(key) == m.end(); }

}

#endif
