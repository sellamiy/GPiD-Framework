#ifndef GPID_ABSTRACT_SOLVER_HPP
#define GPID_ABSTRACT_SOLVER_HPP

#include <gpid/config.hpp>
#include <gpid/core/hypotheses.hpp>

namespace gpid {

    enum SolverTestStatus {
        SOLVER_SAT,
        SOLVER_UNSAT,
        SOLVER_UNKNOWN
    };

#ifdef DEFINE_TRUE_SOLVER
    /** The True Solver : Example Solver interface class. */
    class TrueSolver {
    public:
        struct ProblemT    { };
        struct HypothesisT { };
        struct ModelT
        {
            inline bool isSkippable
            (HypothesisT& hypothesis __attribute__((unused)))
            { return false; }
        };
        std::vector<HypothesisT> sst_int;
        ModelT sst_mdl;
    public:
        inline void setProblem(ProblemT& problem __attribute__((unused))) { }
        inline void start() { }
        inline std::vector<HypothesisT>& extractActive() { return sst_int; }
        inline void addHypothesis
        (HypothesisT& hypothesis __attribute__((unused)), uint32_t level __attribute__((unused))) { }
        inline void removeHypotheses(uint32_t level __attribute__((unused))) { }
        inline SolverTestStatus testHypotheses(uint32_t level __attribute__((unused)))
        { return SolverTestStatus::SOLVER_UNSAT; }
        inline ModelT& recoverModel() { return sst_mdl; }
    };
#endif

};

#endif
