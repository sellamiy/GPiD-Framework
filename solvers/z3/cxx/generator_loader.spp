#ifndef GPID_Z3_GENERATOR_LOADER_SPP
#define GPID_Z3_GENERATOR_LOADER_SPP

using namespace snlog;
using namespace z3;

namespace gpid {

    static inline void loadAbducibles
    (std::string filename, z3::context& ctx, Z3Declarations& decls, HypothesesSet<Z3Solver>& set) {
        alloc_gab<Z3Hypothesis>(set.getSourceSize());
        AbducibleParser parser(filename);
        parser.init();
        for (uint32_t i = 0; i < set.getSourceSize(); i++) {
            if (!parser.isOk()) {
                l_fatal("Error loading from @file:" + filename);
                break;
            }
            std::string expr = parser.nextAbducible();
            std::string smt_assert = "(assert " + expr + ")";
            z3::expr cstl = ctx.parse_string(smt_assert.c_str(), decls.getSortDecls(), decls.getFunDecls());
            store_gab_hyp<HypothesesSet<Z3Solver>, z3::expr>(set, i, cstl);
        }
    }

}
#endif
