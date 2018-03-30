#ifndef GPID_CVC4_CONTEXT_SPP
#define GPID_CVC4_CONTEXT_SPP

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

    struct CVC4Hypothesis {
        CVC4::Expr expr;
        CVC4Hypothesis(CVC4::Expr e) : expr(e) {}
        CVC4Hypothesis(const CVC4Hypothesis& e) : expr(e.expr) {}

        inline const std::string str() const {
            std::stringstream result; result << expr; return result.str();
        }
    };

    struct CVC4ModelWrapper {
        const CVC4::SmtEngine& engine;
        inline CVC4ModelWrapper(CVC4::SmtEngine& engine) : engine(engine) { }
        inline CVC4ModelWrapper(CVC4ModelWrapper& mdlw) : engine(mdlw.engine) { }
        inline bool isSkippable(CVC4Hypothesis& h) const {
            return engine.getValue(h.expr) == engine.getExprManager()->mkConst(true);
        }
    };

}

#endif
