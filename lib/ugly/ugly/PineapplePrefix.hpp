/**
 * \file ugly/PineapplePrefix.hpp
 * \date 2019
 */
#ifndef LIB_UGLY__PINEAPPLE_PREFIX_HPP
#define LIB_UGLY__PINEAPPLE_PREFIX_HPP

#include <set>
#include <string>
#include <snlog/snlog.hpp>
#include <ugly/MapUtils.hpp>

namespace ugly {

    using pineapple_prefix_joint = std::map<std::string, std::string>;
    using pinenapple_sourcefix = std::set<std::string>;

    using pineapple_prefix_tree = std::map<std::string, std::set<std::string>>;

    static inline bool pineprefix(const std::string& p, const std::string& s) {
        return p.length() <= s.length()
            && p == s.substr(0, p.length())
            && std::find_if(s.begin() + p.length(), s.end(), [](char c)
                            { return !std::isdigit(c); }) == s.end();
    }

    static inline size_t pinejuice(const std::string& prefix, const std::string& pineapple) {
        return pineapple.length() == prefix.length() ? 0 : std::stoi(pineapple.substr(prefix.length()));
    }

    static inline const std::string& pinesqueeze_max
    (const std::string& prefix, const pinenapple_sourcefix& globl) {
        auto savior = globl.begin();
        auto priest = globl.begin();
        while (++priest != globl.end()) {
            if (pinejuice(prefix, *priest) > pinejuice(prefix, *savior))
                savior = priest;
        }
        return *savior;
    }

    /** Usual pineapple prefix squeezing algorithm with autostore. */
    inline void pineapple_squeeze_autostore
    (const pinenapple_sourcefix& sf, pineapple_prefix_joint& store) {
        pineapple_prefix_tree tree;
        for (const auto& source : sf) {
            bool alone_in_the_universe = true;
            for (auto& treestored : tree) {
                // source is prefix of tree-stored
                if (pineprefix(source, treestored.first)) {
                    tree[source] = treestored.second;
                    tree.at(source).insert(source);
                    tree.erase(treestored.first);
                    alone_in_the_universe = false;
                    break;
                }
                // source has for prefix a tree-stored
                if (pineprefix(treestored.first, source)) {
                    treestored.second.insert(source);
                    alone_in_the_universe = false;
                    break;
                }
            }
            if (alone_in_the_universe) {
                // source in alone in the universe
                tree[source].insert(source);
            }
        }
        for (const auto& treestored : tree) {
            if (treestored.second.size() > 1) {
                store[treestored.first] = pinesqueeze_max(treestored.first, treestored.second);
            }
        }
    }

    inline pineapple_prefix_joint pineapple_squeeze(const pinenapple_sourcefix& sf) {
        pineapple_prefix_joint store;
        pineapple_squeeze_autostore(sf, store);
        return store;
    }

}

#endif
