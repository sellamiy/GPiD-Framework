#define LIB_SMTLIB2_UTILS__SMTLIB2_TOKEN_RULES_PARSERS_CPP

#include <unordered_set>
#include <smtlib2utils/SMTlib2TokenStringParsers.hpp>

namespace smtlib2utils {

    static inline bool isWhitespace(char c) {
        return c == '\t' || c == '\n' || c == '\r' || c == ' ' ;
    }

    static inline bool isSymbolEnd(char c) {
        return isWhitespace(c) || c == '(' || c == ')';
    }

    static inline bool isDigit(char c) {
        return c == '0' || c == '1' || c == '2' || c == '3' || c == '4'
            || c == '5' || c == '6' || c == '7' || c == '8' || c == '9';
    }

    /*
    static inline bool isNonZeroDigit(char c) {
        return c == '1' || c == '2' || c == '3' || c == '4'
            || c == '5' || c == '6' || c == '7' || c == '8' || c == '9';
    }
    */

    static inline bool isLetter(char c) {
        return c == 'a' || c == 'b' || c == 'c' || c == 'd' || c == 'e'
            || c == 'f' || c == 'g' || c == 'h' || c == 'i' || c == 'j'
            || c == 'k' || c == 'l' || c == 'm' || c == 'n' || c == 'o'
            || c == 'p' || c == 'q' || c == 'r' || c == 's' || c == 't'
            || c == 'u' || c == 'v' || c == 'w' || c == 'x' || c == 'y'
            || c == 'z' || c == 'A' || c == 'B' || c == 'C' || c == 'D'
            || c == 'E' || c == 'F' || c == 'G' || c == 'H' || c == 'I'
            || c == 'J' || c == 'K' || c == 'L' || c == 'M' || c == 'N'
            || c == 'O' || c == 'P' || c == 'Q' || c == 'R' || c == 'S'
            || c == 'T' || c == 'U' || c == 'V' || c == 'W' || c == 'X'
            || c == 'Y' || c == 'Z';
    }

    static inline bool isSymbolAdChar(char c) {
        return c == '+' || c == '-' || c == '/' || c == '*' || c == '='
            || c == '%' || c == '?' || c == '!' || c == '.' || c == '$'
            || c == '_' || c == '~' || c == '&' || c == '^' || c == '<'
            || c == '>' || c == '@';
    }

    static inline bool isSymbolChar(char c) {
        return isDigit(c) || isLetter(c) || isSymbolAdChar(c);
    }

    static inline bool hasMoreChars(const std::string& s, uint32_t pos) {
        return s.length() > pos + 1;
    }

    static inline uint32_t skipWhitespaces(const std::string& s, uint32_t pos) {
        while (s.length() > pos && isWhitespace(s[pos])) ++pos;
        return pos;
    }

    SMTlib2TokenResult nextSimpleSymbol(const std::string& source, uint32_t start) {
        if (source.empty()) return SMTlib2TokenResult(source, start);
        uint32_t nstart = skipWhitespaces(source, start);
        uint32_t pos = nstart;
        if (isDigit(source[pos]))
            return SMTlib2TokenResult(source, start);
        do {
            if (!isSymbolChar(source[pos]))
                return SMTlib2TokenResult(source, start);
        } while (hasMoreChars(source, pos++) && !isSymbolEnd(source[pos]));
        return SMTlib2TokenResult(source, nstart, pos);
    }

    SMTlib2TokenResult nextSymbol(const std::string& source, uint32_t start) {
        if (source.empty()) return SMTlib2TokenResult(source, start);
        uint32_t nstart = skipWhitespaces(source, start);
        if (source[nstart] == '|') {
            uint32_t pos = nstart;
            while (hasMoreChars(source, pos++) && (source[pos]) != '|') {
                if (source[pos] == '\\')
                    return SMTlib2TokenResult(source, start);
            }
            return SMTlib2TokenResult(source, nstart, pos);
        } else {
            return nextSimpleSymbol(source, nstart);
        }
    }

    SMTlib2TokenResult nextKeyword(const std::string& source, uint32_t start) {
        if (source.empty()) return SMTlib2TokenResult(source, start);
        uint32_t nstart = skipWhitespaces(source, start);
        if (source[nstart] == ':') {
            SMTlib2TokenResult temp = nextSimpleSymbol(source, nstart + 1);
            if (temp.valid) {
                return SMTlib2TokenResult(source, nstart, temp.end);
            } else {
                return temp;
            }
        } else {
            return nextSimpleSymbol(source, nstart);
        }
    }

    SMTlib2TokenResult nextNumeral(const std::string& source, uint32_t start) {
        if (source.empty()) return SMTlib2TokenResult(source, start);
        uint32_t nstart = skipWhitespaces(source, start);
        if (!isDigit(source[nstart]))
            return SMTlib2TokenResult(source, start);
        if (source[nstart] == '0') {
            if (isDigit(source[nstart+1])) {
                return SMTlib2TokenResult(source, start);
            } else {
                return SMTlib2TokenResult(source, nstart, nstart+1);
            }
        } else {
            uint32_t pos = nstart;
            while (isDigit(source[pos])) ++pos;
            return SMTlib2TokenResult(source, nstart, pos);
        }
    }

    SMTlib2TokenResult nextIndex(const std::string& source, uint32_t start) {
        if (source.empty()) return SMTlib2TokenResult(source, start);
        uint32_t nstart = skipWhitespaces(source, start);
        if (isDigit(source[nstart])) {
            return nextNumeral(source, nstart);
        } else {
            return nextSymbol(source, nstart);
        }
    }

    SMTlib2TokenResult nextIdentifier(const std::string& source, uint32_t start) {
        if (source.empty()) return SMTlib2TokenResult(source, start);
        uint32_t nstart = skipWhitespaces(source, start);
        if (source[nstart] == '(') {
            uint32_t pos = skipWhitespaces(source, nstart + 1);
            if (source[pos] != '_')
                return SMTlib2TokenResult(source, start);
            SMTlib2TokenResult _symbol = nextSymbol(source, pos);
            pos = _symbol.end;
            do {
                SMTlib2TokenResult _index = nextIndex(source, pos);
                pos = _index.end;
            } while (source[pos] != ')');
            return SMTlib2TokenResult(source, nstart, pos+1);
        } else {
            return nextSymbol(source, nstart);
        }
    }

    SMTlib2TokenResult nextSort(const std::string& source, uint32_t start) {
        if (source.empty()) return SMTlib2TokenResult(source, start);
        uint32_t nstart = skipWhitespaces(source, start);
        if (source[nstart] == '(') {
            uint32_t pos = skipWhitespaces(source, nstart + 1);
            SMTlib2TokenResult _ident = nextIdentifier(source, pos);
            pos = _ident.end;
            do {
                SMTlib2TokenResult _sort = nextSort(source, pos);
                pos = _sort.end;
            } while (source[pos] != ')');
            return SMTlib2TokenResult(source, nstart, pos+1);
        } else {
            return nextIdentifier(source, nstart);
        }
    }

    SMTlib2TokenList nextParameterList__unof(const std::string& source, uint32_t start) {
        if (source.empty()) return SMTlib2TokenList({}, start, start);
        uint32_t nstart = skipWhitespaces(source, start);
        if (source[nstart] != '(')
            return SMTlib2TokenList({}, start, start);
        uint32_t pos = skipWhitespaces(source, nstart + 1);
        std::list<SMTlib2TokenResult> plist;
        while (source[pos] != ')') {
            plist.push_back(nextSort(source, pos));
            pos = skipWhitespaces(source, plist.back().end);
        }
        return SMTlib2TokenList(plist, nstart, pos+1);
    }

}
