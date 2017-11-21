#ifndef GPID_TRUE_SOLVER_INPUTS_HPP
#define GPID_TRUE_SOLVER_INPUTS_HPP

#include <gpid/solvers-wrap/truesolver_engine.hpp>

namespace gpid {

    inline void parse_file(std::string, TrueSolver::ContextManagerT&,
                           TrueSolver::ProblemT&, std::string)
    { snlog::l_info("The True Solver does not need to parse files!"); }

    inline uint32_t countAbducibles(AbduciblesOptions&, TrueSolver::ProblemT&)
    { return 1; }

    inline void generateAbducibles
    (AbduciblesOptions&, TrueSolver::ContextManagerT&,
     TrueSolver::ProblemT::DeclarationsT&, HypothesesSet<TrueSolver>&)
    { }

};

#endif
