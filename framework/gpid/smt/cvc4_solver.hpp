#ifndef GPID_SMT_SOLVER__CVC4_DETAILS_HPP
#define GPID_SMT_SOLVER__CVC4_DETAILS_HPP

#include <gpid/config.hpp>
#include <gpid/smt/cvc4_engine.hpp>

using namespace snlog;

namespace gpid {

    inline void CVC4Solver::removeHypotheses(uint32_t level) {
        snlog::l_warn("Not implemented yet");
    }

    inline void CVC4Solver::addHypothesis(CVC4Hypothesis& hypothesis, uint32_t level) {
        snlog::l_warn("Not implemented yet");
    }

    inline void CVC4Solver::printActiveNegation() {
        snlog::l_warn("Not implemented yet");
    }

    inline void CVC4Solver::storeActive() {
        snlog::l_warn("Not implemented yet");
    }

    inline gpid::SolverTestStatus CVC4Solver::testHypotheses(uint32_t level) {
        snlog::l_warn("Not implemented yet");
        return SolverTestStatus::SOLVER_UNKNOWN;
    }

    inline bool CVC4Solver::currentlySubsumed(CVC4Hypothesis& additional, uint32_t level) {
        snlog::l_warn("Not implemented yet");
        return false;
    }

};

#endif
