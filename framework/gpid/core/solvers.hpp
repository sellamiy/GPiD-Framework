/**
 * \file gpid/core/solvers.hpp
 * \brief GPiD-Framework Solver interfaces elements.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__SOLVERS_HPP
#define GPID_FRAMEWORK__CORE__SOLVERS_HPP

#include <gpid/config.hpp>

namespace gpid {

    /** \brief Generic Wrapper for Solver test results. \ingroup gpidcorelib */
    enum SolverTestStatus {
        /** The formula is satisfiable */
        SOLVER_SAT     = 101,
        /** The formula is unsatisfiable */
        SOLVER_UNSAT   = 110,
        /** The formula satisfiability status cannot be computed */
        SOLVER_UNKNOWN = 111
    };

};

#endif
