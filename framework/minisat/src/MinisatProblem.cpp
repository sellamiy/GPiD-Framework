#define GPID__MINISAT_PROBLEM_CPP

#include <MinisatPropositionalEngine.hpp>

using namespace gpid_prop;

void MinisatProblem::addConstraint(Minisat::vec<Minisat::Lit>& ps) {
    if (mode != IOMode::IO_WRITE) {
        // TODO: Raise Error
    }
    for (int i = 0; i < ps.size(); i++)
        cons_data.push(ps[i]);
    cons_sep.push(ps.size());
}

bool MinisatProblem::hasMoreConstraints() {
    if (mode != IOMode::IO_READ) {
        // TODO: Raise Error
    }
    return read_session_seps.size() > 0;
}

Minisat::vec<Minisat::Lit>& MinisatProblem::nextConstraint() {
    if (mode != IOMode::IO_READ) {
        // TODO: Raise Error
    }
    read_local_data.clear();
    while (read_session_data.size() > read_session_seps.last()) {
        read_local_data.push(read_session_data.last());
        read_session_data.pop();
    }
    read_session_seps.pop();
    return read_local_data;
}

void MinisatProblem::initCurrentMode() {
    switch (mode) {
    case IO_READ:
        cons_sep.copyTo(read_session_seps);
        cons_data.copyTo(read_session_data);
        break;
    case IO_WRITE:
        read_session_seps.clear();
        read_session_data.clear();
        break;
    default:
        // TODO: Raise Error
        break;
    }
}
