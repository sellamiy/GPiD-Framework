#define GPID__MINISAT_PROBLEM_CPP

#include <snlog/snlog.hpp>
#include <gpid/propositional/minisat_pengine.hpp>

using namespace snlog;
using namespace gpid;

void MinisatProblem::addConstraint(Minisat::vec<Minisat::Lit>& ps) {
    if (mode != IOMode::IO_WRITE) {
        // TODO: Raise Error
        l_warn("Writing problem on reading mode!");
    }
    cons_sep.push(cons_data.size());
    for (int i = 0; i < ps.size(); i++)
        cons_data.push(ps[i]);
}

bool MinisatProblem::hasMoreConstraints() {
    if (mode != IOMode::IO_READ) {
        // TODO: Raise Error
        l_warn("Reading problem on writing mode!");
    }
    return read_session_seps.size() > 0;
}

Minisat::vec<Minisat::Lit>& MinisatProblem::nextConstraint() {
    if (mode != IOMode::IO_READ) {
        // TODO: Raise Error
        l_warn("Reading problem on writing mode!");
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
        l_internal("Minisat problem ended in an Unknown state!");
        break;
    }
}
