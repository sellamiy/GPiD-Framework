#ifndef GPID_TRUE_SOLVER_EXAMPLE_HPP
#define GPID_TRUE_SOLVER_EXAMPLE_HPP

#include <gpid/config.hpp>
#include <gpid/core/hypotheses.hpp>

namespace gpid {

    /** The True Solver : Example Solver interface class. */
    class TrueSolver {
    public:
        struct HypothesisT { };
        struct StorageT    { };
        struct ContextManagerT { };
        struct ProblemT    {
            ProblemT(ContextManagerT&) { }
            struct DeclarationsT { };
            DeclarationsT sst_decl;
            inline DeclarationsT& getDeclarations() { return  sst_decl; }
        };
        struct ModelT
        { inline bool isSkippable (HypothesisT&) const { return false; } };
        std::vector<HypothesisT> sst_int;
        ModelT sst_mdl;
        StorageT sst_str;
        ContextManagerT sst_ctm;
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
        inline ContextManagerT& getContextManager() { return sst_ctm; }
        inline bool storageSubsumed (HypothesisT&, uint32_t) { return false; }
        inline void printSolverInformations()
        { snlog::l_info("True Solver - The One True Solver"); }
    };

};

#endif
