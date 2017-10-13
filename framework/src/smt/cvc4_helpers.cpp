#define CVC4_GENERATION_HELPERS
#include <snlog/snlog.hpp>
#include <starray/starray.hpp>
#include <gpid/smt/cvc4_engine.hpp>

using namespace snlog;
using namespace starray;
using namespace CVC4;

static const std::string c4helpers_gab_tag = "CVC4Hypotheses";

extern void gpid::initRawSet(ExprManager& em, CVC4HypothesesSet& set) {
    GAB_Status res;
    res = requestContinuousArray(c4helpers_gab_tag, set.getSourceSize(), sizeof(CVC4Hypothesis));
    if (res != GAB_Status::SUCCESS) l_error("Memory request for minisat hypotheses wrappers failed!");
    for (uint32_t i = 0; i < set.getSourceSize(); i++) {
        Expr cstl = em.mkConst(false);
        l_warn("Fixme: add correct abducible instanciation for cvc4 expression instances"); // TODO
        CVC4Hypothesis *mloc;
        res = accessContinuousPointer(c4helpers_gab_tag, i, (void**)&mloc);
        if (res != GAB_Status::SUCCESS) l_error("Memory access for minisat hypothesis wrapper failed!");
        new (mloc) CVC4Hypothesis(cstl);
        set.mapHypothesis(i, mloc);
        // set.mapLink(i, i%2 == 0 ? i+1 : i-1); // TODO Linkage
        l_warn("Fixme: possibly, add abducible linkage for cvc4 expression instances"); // TODO
    }
}
