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

#ifdef TRUE_SOLVER_INTERFACE
    /** The True Solver : Example Solver interface class. */
    class TrueSolver {
    public:
        struct ProblemT    { };
        struct HypothesisT { };
        struct StorageT    { };
        struct ModelT
        { inline bool isSkippable (HypothesisT&) const { return false; } };
        std::vector<HypothesisT> sst_int;
        ModelT sst_mdl;
        StorageT sst_str;
    public:
        inline void setProblem(ProblemT&) { }
        inline void start() { }
        inline std::vector<HypothesisT>& extractActive() { return sst_int; }
        inline void addHypothesis
        (HypothesisT&, uint32_t) { }
        inline void removeHypotheses(uint32_t) { }
        inline SolverTestStatus testHypotheses(uint32_t)
        { return SolverTestStatus::SOLVER_UNSAT; }
        inline SolverTestStatus checkConsistency(uint32_t)
        { return SolverTestStatus::SOLVER_SAT; }
        inline void printActiveNegation() { }
        inline void storeActive() { }
        inline ModelT& recoverModel() { return sst_mdl; }
        inline StorageT& getStorage() { return sst_str; }
        inline bool storageSubsumed (HypothesisT&, uint32_t) { return false; }
    };
#endif

};

#endif
