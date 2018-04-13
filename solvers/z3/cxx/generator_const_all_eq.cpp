#ifndef GPID_Z3_GENERATOR_CONST_ALL_EQ_SPP
#define GPID_Z3_GENERATOR_CONST_ALL_EQ_SPP

using namespace snlog;
using namespace z3;

namespace gpid {

    static inline uint32_t countAbducibles_constAllEq(z3::context&, Z3Declarations& decls) {
        uint32_t l_gvr = decls.getFunDecls().size();
        return l_gvr > 1 ? l_gvr * (l_gvr - 1) : 0;
    }

    static inline
    void generateAbducibles_constAllEq(z3::context&, Z3Declarations& decls,
                                       HypothesesEngine<Z3Solver>& set) {
        alloc_gab<Z3Hypothesis>(set.getSourceSize());
        uint32_t vCount = decls.getFunDecls().size();
        uint32_t pos = 0;
        for (uint32_t i = 0; i < vCount; i++) {
            for (uint32_t j = i+1; j < vCount; j++) {
                z3::expr cstl_eq = decls.getFunDecls()[i]() == decls.getFunDecls()[j]();
                z3::expr cstl_neq = decls.getFunDecls()[i]() != decls.getFunDecls()[j]();
                store_gab_hyp<HypothesesEngine<Z3Solver>, z3::expr>(set, pos, cstl_eq);
                store_gab_hyp<HypothesesEngine<Z3Solver>, z3::expr>(set, pos+1, cstl_neq);
                set.mapLink(pos, pos+1);
                set.mapLink(pos+1, pos);
                pos += 2;
            }
        }
    }

}

#endif
