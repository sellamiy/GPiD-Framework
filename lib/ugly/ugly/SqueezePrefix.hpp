/**
 * \file ugly/SqueezePrefix.hpp
 * \date 2019
 */
#ifndef LIB_UGLY__SQUEEZE_PREFIX_HPP
#define LIB_UGLY__SQUEEZE_PREFIX_HPP

#include <set>
#include <string>
#include <algorithm>
#include <snlog/snlog.hpp>
#include <ugly/MapUtils.hpp>

namespace ugly {

    using squeeze_prefix_joint = std::map<std::string, std::string>;
    using squeeze_sourcefix = std::set<std::string>;

    using squeeze_prefix_tree = std::map<std::string, std::set<std::string>>;

    static inline bool sqprefix(const std::string& p, const std::string& s) {
        return p.length() <= s.length()
            && p == s.substr(0, p.length())
            && std::find_if(s.begin() + p.length(), s.end(), [](char c)
                            { return !std::isdigit(c); }) == s.end();
    }

    static inline size_t sqjuice(const std::string& prefix, const std::string& squeeze) {
        return squeeze.length() == prefix.length() ? 0 : std::stoi(squeeze.substr(prefix.length()));
    }

    static inline const std::string& squeeze_max
    (const std::string& prefix, const squeeze_sourcefix& globl) {
        auto savior = globl.begin();
        auto priest = globl.begin();
        while (++priest != globl.end()) {
            if (sqjuice(prefix, *priest) > sqjuice(prefix, *savior))
                savior = priest;
        }
        return *savior;
    }

    /** Usual squeeze prefix squeezing algorithm with autostore. */
    inline void squeeze_autostore
    (const squeeze_sourcefix& sf, squeeze_prefix_joint& store) {
        squeeze_prefix_tree tree;
        for (const auto& source : sf) {
            bool alone_in_the_universe = true;
            for (auto& treestored : tree) {
                // source is prefix of tree-stored
                if (sqprefix(source, treestored.first)) {
                    tree[source] = treestored.second;
                    tree.at(source).insert(source);
                    tree.erase(treestored.first);
                    alone_in_the_universe = false;
                    break;
                }
                // source has for prefix a tree-stored
                if (sqprefix(treestored.first, source)) {
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
                store[treestored.first] = squeeze_max(treestored.first, treestored.second);
            }
        }
    }

    inline squeeze_prefix_joint squeeze(const squeeze_sourcefix& sf) {
        squeeze_prefix_joint store;
        squeeze_autostore(sf, store);
        return store;
    }

}

#endif
