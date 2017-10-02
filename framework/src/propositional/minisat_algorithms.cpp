#define MINISAT_GENERATION_INSTANCES

#include <gpid/propositional/minisat_pengine.hpp>
#include <gpid/propositional/minisat_outputs.hpp>
#include <gpid/algorithms/bpd_algorithm.hpp>

namespace gpid {
    template<>
    extern void DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver>
    ::printAsImplicate(std::vector<MinisatHypothesis>& impl, bool negate) {
        if (negate) {
            std::cout << "> ";
            for (MinisatHypothesis hyp : impl) std::cout << ~(hyp.lit) << " ";
            std::cout << std::endl;
        } else {
            l_warn("Minisat Implicate Non-negated Printers are not implemeted yet!");
        }
    }

    template class DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver>;
};
