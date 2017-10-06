#define MINISAT_GENERATION_INSTANCES

#include <gpid/propositional/minisat_pengine.hpp>
#include <gpid/propositional/minisat_wrapper.hpp>
#include <gpid/propositional/minisat_outputs.hpp>
#include <gpid/algorithms/bpd_algorithm.hpp>
#include <gpid/algorithms/pid_algorithm.hpp>

namespace gpid {
    template<> void DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver, MinisatModelWrapper>
    ::printAsImplicate(std::vector<MinisatHypothesis>& impl, bool negate) {
        p_implicate(std::cout, impl, negate);
    }

    template class DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver, MinisatModelWrapper>;
};
