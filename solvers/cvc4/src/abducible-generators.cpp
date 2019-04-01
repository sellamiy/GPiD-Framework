#define CVC4_API_INTERFACE_FOR_GPID__ABDUCIBLE_GENERATORS__CPP

#include <functional>
#include <cvc4-api-abdgen.hpp>
#include <stdutils/collections.hpp>

using namespace abdulot;

void CVC4AbducibleHandler::allocate(const std::string id, size_t size) {
    memoryRangeAllocation<CVC4Literal>(id, size);
}

void CVC4AbducibleHandler::handleAbducible(const std::string& abd) {
    CVC4::Options opts4;
    snlog::l_warn() << "Fixme: Abducible Parser - input language as an option" << snlog::l_end; // TODO
    opts4.setInputLanguage(CVC4::language::input::LANG_SMTLIB_V2);

    CVC4::ExprManager& em = pbld.getContextManager();
    CVC4::parser::ParserBuilder pb(&em, "<internal>", opts4);
    CVC4::parser::Parser* p = pb.withStringInput(abd).build();
    p->useDeclarationsFrom(pbld.getDeclarations().getSymbolTable());
    CVC4::Expr cstl = p->nextExpression();

    memoryObjectAllocation(abducibles_memory_id, _cpt++, mapper, cstl);
}

CVC4AbducibleLiteralsGenerator::CVC4AbducibleLiteralsGenerator(CVC4ProblemLoader& pbld)
    : pbld(pbld), handler(pbld, mapper, links) {}

size_t CVC4AbducibleLiteralsGenerator::count() const {
    return handler._cpt;
}

void CVC4AbducibleLiteralsGenerator::load(const std::string filename) {
    loadAbducibles(filename, handler);
}

/* Abducible generators */

#include <map>

static inline void cvc4_abduciblesUtils_allEq
(CVC4ProblemLoader& pbld, std::vector<CVC4::Expr>& knownVars) {
    CVC4::ExprManager& ctx = pbld.getContextManager();
    /*
     * Delegate symbol accesses to a dummy parser as direct accesses
     * to the symbolTable seem to raise segmentation faults.
     */
    CVC4::Options opts4;
    opts4.setInputLanguage(CVC4::language::input::LANG_SMTLIB_V2);
    CVC4::parser::ParserBuilder pb(&ctx, "<internal>", opts4);
    CVC4::parser::Parser* p = pb.withStringInput("").build();
    p->useDeclarationsFrom(pbld.getDeclarations().getSymbolTable());

    /* Building a type table for abducible generation */
    std::map<CVC4::Type, std::vector<CVC4::Expr>> typeTable;
    for (const std::string decl : pbld.getDeclarations()) {
        CVC4::Expr fun = p->getFunction(decl);
        if (fun.getType().isFunction()) {
            snlog::l_warn()
                << "Function are currently not handles by this CVC4 abducible generator" << snlog::l_end;
            // TODO : Handle functions
            // snlog::l_info() << fun.getType() << snlog::l_end;
            // snlog::l_info() << fun.getType().getBaseType() << snlog::l_end;
        } else {
            knownVars.push_back(fun);
            typeTable[fun.getType()].push_back(fun);
        }
    }
}

static inline size_t abdgen_cvc4_allEq
(CVC4ProblemLoader& pbld, ObjectMapper<CVC4Literal>& mapper,
 std::map<uint32_t, std::vector<uint32_t>>& links) {
    CVC4::ExprManager& ctx = pbld.getContextManager();
    std::vector<CVC4::Expr> knownVars;
    cvc4_abduciblesUtils_allEq(pbld, knownVars);
    size_t size = knownVars.size() > 1 ? knownVars.size() * (knownVars.size() - 1) : 0;
    
    /* Building abducibles */
    uint32_t pos = 0;
    memoryRangeAllocation<CVC4Literal>(abducibles_memory_id, size);
    for (uint32_t i = 0; i < knownVars.size(); i++) {
        for (uint32_t j = i + 1; j < knownVars.size(); j++) {
            CVC4::Expr eq_expr  = ctx.mkExpr(CVC4::kind::EQUAL, knownVars[i], knownVars[j]);
            CVC4::Expr neq_expr = ctx.mkExpr(CVC4::kind::DISTINCT, knownVars[i], knownVars[j]);
            memoryObjectAllocation(abducibles_memory_id, pos, mapper, eq_expr);
            memoryObjectAllocation(abducibles_memory_id, pos+1, mapper, neq_expr);
            links[pos].push_back(pos+1);
            links[pos+1].push_back(pos);
            pos += 2;
        }
    }

    return size;
}

using AbdgenFunctionT = std::function<size_t(CVC4ProblemLoader&, ObjectMapper<CVC4Literal>&,
                                             std::map<uint32_t, std::vector<uint32_t>>&)>;
static std::map<std::string, AbdgenFunctionT> abg_cvc4_abdgeneration_table = {
    { "all-eq", AbdgenFunctionT(abdgen_cvc4_allEq) },
    { "default", AbdgenFunctionT(abdgen_cvc4_allEq) }
};

void CVC4AbducibleLiteralsGenerator::generate(const std::string generator) {
    if (stdutils::inmap(abg_cvc4_abdgeneration_table, generator)) {
        handler._cpt = abg_cvc4_abdgeneration_table[generator](pbld, mapper, links);
    } else {
        snlog::l_fatal() << "Unknown cvc4 abducible generator: " << generator << snlog::l_end;
    }
}
