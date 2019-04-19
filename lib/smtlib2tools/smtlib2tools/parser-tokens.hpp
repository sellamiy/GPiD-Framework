/**
 * \file smtlib2tools/parser-tokens.hpp
 * \brief Smtlib2 token parser.
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_TOKEN_STRING_PARSERS_HPP
#define LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_TOKEN_STRING_PARSERS_HPP

#include <smtlib2tools/core.hpp>

namespace smtlib2 {

    struct SMTlib2TokenResult {
        const std::string& source;
        const uint32_t start, end;
        const bool valid;

        inline std::string value() const {
            return source.substr(start, end-start);
        }

        SMTlib2TokenResult(const std::string& source, uint32_t start)
            : source(source), start(start), end(start), valid(false) {}
        SMTlib2TokenResult(const std::string& source, uint32_t start, uint32_t end)
            : source(source), start(start), end(end), valid(true) {}
        SMTlib2TokenResult(const SMTlib2TokenResult& o)
            : source(o.source), start(o.start), end(o.end), valid(o.valid) {}
    };

    struct SMTlib2TokenList {
        const std::vector<SMTlib2TokenResult> content;
        const uint32_t start, end;

        inline std::vector<std::string> value() const {
            std::vector<std::string> res;
            for (auto tk : content) res.push_back(tk.value());
            return res;
        }

        inline const SMTlib2TokenResult& first() const { return content.front(); }
        inline const SMTlib2TokenResult& last() const { return content.back(); }
        inline constexpr size_t size() const { return content.size(); }

        SMTlib2TokenList(const std::vector<SMTlib2TokenResult>& tkl)
            : content(tkl), start(tkl.front().start), end(tkl.back().end) {}
        SMTlib2TokenList(const std::vector<SMTlib2TokenResult>& tkl, uint32_t start, uint32_t end)
            : content(tkl), start(start), end(end) {}
        SMTlib2TokenList(const SMTlib2TokenList& o)
            : content(o.content), start(o.start), end(o.end) {}
    };

    inline bool isReserved(const SMTlib2TokenResult& tk) {
        return is_reserved(tk.value());
    }

    SMTlib2TokenResult nextSimpleSymbol(const std::string& source, uint32_t start=0);
    inline SMTlib2TokenResult nextSimpleSymbol(const SMTlib2TokenResult& tk) {
        return nextSimpleSymbol(tk.source, tk.end);
    }

    SMTlib2TokenResult nextSymbol(const std::string& source, uint32_t start=0);
    inline SMTlib2TokenResult nextSymbol(const SMTlib2TokenResult& tk) {
        return nextSymbol(tk.source, tk.end);
    }

    SMTlib2TokenResult nextKeyword(const std::string& source, uint32_t start=0);
    inline SMTlib2TokenResult nextKeyword(const SMTlib2TokenResult& tk) {
        return nextKeyword(tk.source, tk.end);
    }

    SMTlib2TokenResult nextNumeral(const std::string& source, uint32_t start=0);
    inline SMTlib2TokenResult nextNumeral(const SMTlib2TokenResult& tk) {
        return nextNumeral(tk.source, tk.end);
    }

    SMTlib2TokenResult nextIndex(const std::string& source, uint32_t start=0);
    inline SMTlib2TokenResult nextIndex(const SMTlib2TokenResult& tk) {
        return nextIndex(tk.source, tk.end);
    }

    SMTlib2TokenResult nextIdentifier(const std::string& source, uint32_t start=0);
    inline SMTlib2TokenResult nextIdentifier(const SMTlib2TokenResult& tk) {
        return nextIdentifier(tk.source, tk.end);
    }

    SMTlib2TokenResult nextSort(const std::string& source, uint32_t start=0);
    inline SMTlib2TokenResult nextSort(const SMTlib2TokenResult& tk) {
        return nextSort(tk.source, tk.end);
    }

    SMTlib2TokenList nextParameterList__unof(const std::string& source, uint32_t start=0);
    inline SMTlib2TokenList nextParameterList__unof(const SMTlib2TokenResult& tk) {
        return nextParameterList__unof(tk.source, tk.end);
    }

    SMTlib2TokenList nextParameterListNoPar__unof(const std::string& source, uint32_t start=0);
    inline SMTlib2TokenList nextParameterListNoPar__unof(const SMTlib2TokenResult& tk) {
        return nextParameterListNoPar__unof(tk.source, tk.end);
    }

}

#endif
