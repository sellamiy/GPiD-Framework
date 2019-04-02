/**
 * \file stdutils/strings.hpp
 * \brief Misc. utils for standard library's strings
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_STANDARD_UTILS__STRINGS_HPP
#define LIB_STANDARD_UTILS__STRINGS_HPP

#include <string>
#include <sstream>
#include <vector>

namespace stdutils {

    static inline const std::vector<std::string> split(const std::string& src, const std::string& delim) {
        size_t _0P = 0;
        size_t _1P = 0;
        std::string tk;
        std::vector<std::string> res;
        while ((_1P = src.find(delim, _0P)) != std::string::npos) {
            tk = src.substr(_0P, _1P - _0P);
            res.push_back(tk);
            _0P = _1P += delim.length();
        }
        tk = src.substr(_0P);
        res.push_back(tk);
        return res;
    }

    static inline size_t count(const std::string& src, const std::string& tgt) {
        size_t occ = 0;
        size_t _0P = 0;
        while ((_0P = src.find(tgt, _0P)) != std::string::npos) {
            ++occ;
            _0P += tgt.length();
        }
        return occ;
    }

    static inline std::string join(const std::string& jer, const std::vector<std::string>& elems) {
        if (elems.size() == 0) return "";
        if (elems.size() == 1) return elems.front();
        std::stringstream res;
        bool start = true;
        for (auto elem : elems) {
            if (start) {
                res << elem;
                start = false;
            } else {
                res << jer << elem;
            }
        }
        return res.str();
    }

}

#endif
