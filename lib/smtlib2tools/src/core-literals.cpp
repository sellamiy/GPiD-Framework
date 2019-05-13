#define LIB_SMTLIB2_UTILS__SMTLIB2_LITERALS_CHECK_CPP

#include <unordered_set>
#include <smtlib2tools/core.hpp>

namespace smtlib2 {

    enum class LSM_SE { Undirected, Sharped, String, Hexd, Bind, Int, Dec, Failure };

    static constexpr bool isdigit(const char& c) {
        return c == '1' || c == '2' || c == '3' || c == '4' || c == '5' ||
            c == '6' || c == '7' || c == '8' || c == '9' || c == '0';
    }

    static constexpr bool isbindigit(const char& c) {
        return c == '1' || c == '0';
    }

    static constexpr bool ishexdigit(const char& c) {
        return isdigit(c) || c == 'a' || c == 'b' || c == 'c' || c == 'd' || c == 'e' || c == 'f' ||
            c == 'A' || c == 'B' || c == 'C' || c == 'D' || c == 'E' || c == 'F';
    }

    extern bool is_literal(const smtident_t& word) {
        LSM_SE state = LSM_SE::Undirected;
        for (const char& c : word) {
            switch (state) {
            case LSM_SE::Undirected:
                if (isdigit(c) || c == '-') state = LSM_SE::Int;
                else if (c == '#') state = LSM_SE::Sharped;
                else if (c == '"') state = LSM_SE::String;
                else return false;
                break;

            case LSM_SE::Sharped:
                if (c == 'x') state = LSM_SE::Hexd;
                else if (c == 'b') state = LSM_SE::Bind;
                else return false;
                break;

            case LSM_SE::String:
                if (c == '"') state = LSM_SE::Failure;
                // This produces failure iff c is not the last character of word
                break;

            case LSM_SE::Hexd:
                if (!ishexdigit(c)) return false;
                break;

            case LSM_SE::Bind:
                if (!isbindigit(c)) return false;
                break;

            case LSM_SE::Int:
                if (c == '.') state = LSM_SE::Dec;
                break;

            case LSM_SE::Dec:
                if (!isdigit(c)) return false;
                break;

            case LSM_SE::Failure:                
            default:
                return false;
            }
        }
        return true;
    }

}
