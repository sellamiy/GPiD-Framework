#ifndef GPID_MINISAT_PROBLEM_SRC_SPP
#define GPID_MINISAT_PROBLEM_SRC_SPP

#include <snlog/snlog.hpp>

using namespace snlog;
using namespace gpid;

namespace gpid {

    class MinisatProblemInternal {
    public:
        Minisat::vec<Minisat::Lit> cons_data;
        Minisat::vec<int> cons_sep;

        Minisat::vec<int> read_session_seps;
        Minisat::vec<Minisat::Lit> read_session_data;
        Minisat::vec<Minisat::Lit> read_local_data;

        inline void addConstraint(Minisat::vec<Minisat::Lit>& ps) {
            cons_sep.push(cons_data.size());
            for (int i = 0; i < ps.size(); i++)
                cons_data.push(ps[i]);
        }

        inline void goToNextConstraint() {
            read_local_data.clear();
            while (read_session_data.size() > read_session_seps.last()) {
                read_local_data.push(read_session_data.last());
                read_session_data.pop();
            }
            read_session_seps.pop();
        }
    };

}

MinisatProblem::MinisatProblem(MinisatContextManager& ctx)
    : handler(new MinisatProblemInternal()), ctx(ctx) { }

MinisatProblem::~MinisatProblem() { }

void MinisatProblem::addConstraint(Minisat::vec<Minisat::Lit>& ps) {
    if (mode != IOMode::IO_WRITE) {
        // TODO: Raise Error
        l_warn("Writing problem on reading mode!");
    }
    handler->addConstraint(ps);
}

bool MinisatProblem::hasMoreConstraints() {
    if (mode != IOMode::IO_READ) {
        // TODO: Raise Error
        l_warn("Reading problem on writing mode!");
    }
    return handler->read_session_seps.size() > 0;
}

Minisat::vec<Minisat::Lit>& MinisatProblem::nextConstraint() {
    if (mode != IOMode::IO_READ) {
        // TODO: Raise Error
        l_warn("Reading problem on writing mode!");
    }
    handler->goToNextConstraint();
    return handler->read_local_data;
}

void MinisatProblem::initCurrentMode() {
    switch (mode) {
    case IO_READ:
        handler->cons_sep.copyTo(handler->read_session_seps);
        handler->cons_data.copyTo(handler->read_session_data);
        break;
    case IO_WRITE:
        handler->read_session_seps.clear();
        handler->read_session_data.clear();
        break;
    default:
        // TODO: Raise Error
        l_internal("Minisat problem ended in an Unknown state!");
        break;
    }
}

#endif
