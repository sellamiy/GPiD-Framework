#ifndef GPID_CVC4_CONTEXT_HPP
#define GPID_CVC4_CONTEXT_HPP

#include <vector>
#include <cvc4/cvc4.h>

namespace gpid {

    class CVC4Declarations {
        std::vector<std::string> nameDefs;
        CVC4::SymbolTable* stable;
    public:
        inline CVC4::SymbolTable* getSymbolTable() { return stable; }
        inline std::vector<std::string>::iterator begin() { return nameDefs.begin(); }
        inline std::vector<std::string>::iterator end()   { return nameDefs.end(); }
        inline std::vector<std::string>::const_iterator cbegin() { return nameDefs.cbegin(); }
        inline std::vector<std::string>::const_iterator cend()   { return nameDefs.cend(); }

        void store(CVC4::SymbolTable* table);
        void collect(CVC4::Command* cmd);
    };

};

#endif
