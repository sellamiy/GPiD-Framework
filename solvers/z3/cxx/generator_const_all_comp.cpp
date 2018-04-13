#ifndef GPID_Z3_GENERATOR_CONST_ALL_COMP_SPP
#define GPID_Z3_GENERATOR_CONST_ALL_COMP_SPP

using namespace snlog;
using namespace z3;

namespace gpid {

    static inline uint32_t countAbducibles_constAllComp(z3::context&, Z3Declarations& decls) {
        uint32_t l_gvr = decls.getFunDecls().size();
        return l_gvr > 1 ? l_gvr * (l_gvr - 1) * 2 : 0;
    }

    static inline
    void generateAbducibles_constAllComp(z3::context&, Z3Declarations& decls,
                                         HypothesesEngine<Z3Solver>& set) {
        alloc_gab<Z3Hypothesis>(set.getSourceSize());
        uint32_t vCount = decls.getFunDecls().size();
        uint32_t pos = 0;
        for (uint32_t i = 0; i < vCount; i++) {
            for (uint32_t j = i+1; j < vCount; j++) {
                z3::expr cstl_gt = decls.getFunDecls()[i]() >  decls.getFunDecls()[j]();
                z3::expr cstl_ge = decls.getFunDecls()[i]() >= decls.getFunDecls()[j]();
                z3::expr cstl_lt = decls.getFunDecls()[i]() <  decls.getFunDecls()[j]();
                z3::expr cstl_le = decls.getFunDecls()[i]() <= decls.getFunDecls()[j]();
                store_gab_hyp<HypothesesEngine<Z3Solver>, z3::expr>(set, pos, cstl_gt);
                store_gab_hyp<HypothesesEngine<Z3Solver>, z3::expr>(set, pos+1, cstl_ge);
                store_gab_hyp<HypothesesEngine<Z3Solver>, z3::expr>(set, pos+2, cstl_lt);
                store_gab_hyp<HypothesesEngine<Z3Solver>, z3::expr>(set, pos+3, cstl_le);
                set.mapLink(pos, pos+1);
                set.mapLink(pos, pos+2);
                set.mapLink(pos, pos+3);
                set.mapLink(pos+1, pos+2);
                set.mapLink(pos+1, pos+3);
                set.mapLink(pos+2, pos+3);
                set.mapLink(pos+1, pos);
                set.mapLink(pos+2, pos);
                set.mapLink(pos+3, pos);
                set.mapLink(pos+2, pos+1);
                set.mapLink(pos+3, pos+1);
                set.mapLink(pos+3, pos+2);
                pos += 4;
            }
        }
    }

}

#endif
