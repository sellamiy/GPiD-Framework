#define Z3_GENERATION_HELPERS
#include <snlog/snlog.hpp>
#include <starray/starray.hpp>
#include <gpid/smt/z3_engine.hpp>

using namespace snlog;
using namespace starray;
using namespace z3;

static const std::string z3helpers_gab_tag = "Z3Hypotheses";

extern void gpid::initRawSet(context& ctx, Z3HypothesesSet& set) {
    GAB_Status res;
    res = requestContinuousArray(z3helpers_gab_tag, set.getSourceSize(), sizeof(Z3Hypothesis));
    t_error(res != GAB_Status::SUCCESS, "Memory request for minisat hypotheses wrappers failed!");
    for (uint32_t i = 0; i < set.getSourceSize(); i++) {
        expr cstl = ctx.bool_val(true);
        l_warn("Fixme: add correct abducible instanciation for z3 expression instances"); // TODO
        Z3Hypothesis *mloc;
        res = accessContinuousPointer(z3helpers_gab_tag, i, (void**)&mloc);
        t_error(res != GAB_Status::SUCCESS, "Memory access for minisat hypothesis wrapper failed!");
        new (mloc) Z3Hypothesis(cstl);
        set.mapHypothesis(i, mloc);
        // set.mapLink(i, i%2 == 0 ? i+1 : i-1); // TODO Linkage
        l_warn("Fixme: possibly, add abducible linkage for z3 expression instances"); // TODO
    }
}
