#ifndef GPID_Z3_GENERATOR_LOADER_SPP
#define GPID_Z3_GENERATOR_LOADER_SPP

using namespace snlog;
using namespace z3;

namespace gpid {

    static inline void loadAbducible
    (int idx, const std::string expr,
     z3::context& ctx, Z3Declarations& decls,
     LiteralsEngine<Z3Solver>& set, std::map<int, int>&) {
        std::string smt_assert = "(assert " + expr + ")";
        z3::expr cstl = ctx.parse_string(smt_assert.c_str(), decls.getSortDecls(), decls.getFunDecls());
        store_gab_hyp<LiteralsEngine<Z3Solver>, z3::expr>(set, idx, cstl);
    }

}
#endif
