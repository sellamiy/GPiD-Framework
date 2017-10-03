#define MINISAT_GENERATION_HELPERS
#include <starray/starray.hpp>
#include <gpid/errors.hpp>
#include <gpid/propositional/minisat_pengine.hpp>

using namespace starray;
using namespace Minisat;

static std::string mhelpers_gab_tag = "MinisatHypotheses";

extern void gpid::initRawSet(gpid::MinisatHypothesesSet& set) {
    GAB_Status res;
    res = requestContinuousArray(mhelpers_gab_tag, set.getSourceSize(), sizeof(MinisatHypothesis));
    if (res != GAB_Status::SUCCESS) l_error("Memory request for minisat hypotheses wrappers failed!");
    for (uint32_t i = 0; i < set.getSourceSize(); i++) {
        Lit cstl;
        cstl.x = i;
        MinisatHypothesis *mloc;
        res = accessContinuousPointer(mhelpers_gab_tag, i, (void**)&mloc);
        if (res != GAB_Status::SUCCESS) l_error("Memory access for minisat hypothesis wrapper failed!");
        new (mloc) MinisatHypothesis(cstl);
        set.mapHypothesis(i, mloc);
    }
}
