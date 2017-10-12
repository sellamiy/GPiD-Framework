#define GPID__CVC4_PROBLEM_CPP

#include <snlog/snlog.hpp>
#include <gpid/smt/cvc4_engine.hpp>

using namespace snlog;
using namespace gpid;

void CVC4Problem::addConstraint(CVC4::Expr cons) {
    t_warn(mode != IOMode::IO_WRITE, "Writing problem on reading mode");
    cons_data.push_back(cons);
}

bool CVC4Problem::hasMoreConstraints() {
    t_warn(mode != IOMode::IO_READ, "Reading problem on writing mode");
    return reading_pos < cons_data.size();
}

CVC4::Expr& CVC4Problem::nextConstraint() {
    t_warn(mode != IOMode::IO_READ, "Reading problem on writing mode");
    return cons_data[reading_pos++];
}

void CVC4Problem::initCurrentMode() {
    switch (mode) {
    case IO_READ:
        reading_pos = 0;
        break;
    case IO_WRITE:
        reading_pos = -1;
        break;
    default:
        // TODO: Raise Error
        l_internal("Minisat problem ended in an Unknown state!");
        break;
    }
}
