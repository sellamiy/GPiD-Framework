#ifndef GPID_CVC4_CONTEXT_HPP
#define GPID_CVC4_CONTEXT_HPP

#include <vector>
#include <cvc4/cvc4.h>

namespace gpid {

    class CVC4Declarations {
        CVC4::SymbolTable* stable;
    public:
        inline CVC4::SymbolTable* getSymbolTable() { return stable; }

        void collect(CVC4::SymbolTable* table);
    };

};

#endif
