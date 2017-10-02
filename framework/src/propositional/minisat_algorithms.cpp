#define MINISAT_GENERATION_INSTANCES

#include <gpid/propositional/minisat_pengine.hpp>
#include <gpid/algorithms/bpd_algorithm.hpp>

namespace gpid {
    template<>
    extern void DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver>
    ::printAsImplicate(std::vector<MinisatHypothesis>& impl, bool negate) {
        if (negate) {
            l_warn("Minisat Implicate Negated Printers are not complete yet!");
            std::cout << "+ ";
            for (MinisatHypothesis hyp : impl) std::cout /* << ~(hip.lit) */ << " ";
            std::cout << std::endl;
        } else {
            l_warn("Minisat Implicate Non-negated Printers are not implemeted yet!");
        }
    }

    template class DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver>;
};
