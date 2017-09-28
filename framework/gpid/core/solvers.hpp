#ifndef GPID_ABSTRACT_SOLVER_HPP
#define GPID_ABSTRACT_SOLVER_HPP

#include <gpid/core/hypotheses.hpp>

namespace gpid {

    enum SolverTestStatus {
        SOLVER_SAT,
        SOLVER_UNSAT,
        SOLVER_UNKNOWN
    };

};

#endif
