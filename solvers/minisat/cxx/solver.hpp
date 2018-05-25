#ifndef GPID_MINISAT_SOLVER_SPP
#define GPID_MINISAT_SOLVER_SPP

#include <sstream>

using namespace snlog;

namespace gpid {

    class MinisatSolverInternal {
    public:
        Minisat::SimpSolver solver;
        MinisatModelWrapper iw_mdl;
        Minisat::vec<Minisat::Lit> assumps;
        std::vector<MinisatLiteral> loc_ass;
        Minisat::vec<int> lvl_stack;

        MinisatSolverInternal() : iw_mdl(solver.model)
        {
            solver.eliminate(true);
            solver.verbosity = 0;
        }

        inline void push() {
            lvl_stack.push(assumps.size());
        }

        inline void pop() {
            while (assumps.size() > lvl_stack.last()) {
                assumps.pop();
                loc_ass.pop_back();
            }
            lvl_stack.pop(); // TODO: Check that this modification works after storage is reestablished
        }
    };

    inline void MinisatSolverInterface::push() { _internal->push(); }

    inline void MinisatSolverInterface::pop() { _internal->pop(); }

    inline void MinisatSolverInterface::addLiteral(MinisatLiteral& literal) {
        _internal->loc_ass.push_back(literal);
        _internal->assumps.push(literal.lit);
    }

    inline MinisatModelWrapper& MinisatSolverInterface::getModel() {
        return _internal->iw_mdl;
    }

    inline void MinisatSolverInterface::printAssertions(bool negated) {
        p_implicate(std::cout, _internal->assumps, negated);
    }

    inline const std::string MinisatSolverInterface::getPrintableAssertions(bool) {
        std::stringstream result;
        result << _internal->assumps;
        return result.str();
    }

    inline gpid::SolverTestStatus MinisatSolverInterface::check() {
        Minisat::lbool ret = _internal->solver.solveLimited(_internal->assumps);
        if      (ret == Minisat::l_True)  return gpid::SolverTestStatus::SAT;
        else if (ret == Minisat::l_False) return gpid::SolverTestStatus::UNSAT;
        else                              return gpid::SolverTestStatus::UNKNOWN;
    }

}

#endif
