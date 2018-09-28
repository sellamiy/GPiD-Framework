#ifndef LIB_SMTLIB2_UTILS__SMTLIB2_TOKEN_STRING_PARSERS_HPP
#define LIB_SMTLIB2_UTILS__SMTLIB2_TOKEN_STRING_PARSERS_HPP

#include <string>

namespace smtlib2utils {

    struct SMTlib2TokenResult {
        const std::string& source;
        const std::string value;
        const uint32_t start, end;

        SMTlib2TokenResult(std::string& source, std::string value, uint32_t start, uint32_t end)
            : source(source), value(value), start(start), end(end) {}
        SMTlib2TokenResult(const SMTlib2TokenResult& o)
            : source(o.source), value(o.value), start(o.start), end(o.end) {}
    };

    bool isReservedKeyword(const std::string word);
    inline bool isReservedKeyword(const SMTlib2TokenResult& tk) {
        return isReservedKeyword(tk.value);
    }

}

#endif
