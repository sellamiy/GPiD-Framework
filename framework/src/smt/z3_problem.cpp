#define GPID__Z3_PROBLEM_CPP

#include <snlog/snlog.hpp>
#include <gpid/smt/z3_engine.hpp>

using namespace snlog;
using namespace gpid;

void Z3Problem::addConstraint(z3::expr cons, z3::context& ctx) {
    t_warn(mode != IOMode::IO_WRITE, "Writing problem on reading mode");
    cons_data.push_back(cons);
    decls.collect(ctx, cons);
}

bool Z3Problem::hasMoreConstraints() {
    t_warn(mode != IOMode::IO_READ, "Reading problem on writing mode");
    return reading_pos < cons_data.size();
}

z3::expr Z3Problem::nextConstraint() {
    t_warn(mode != IOMode::IO_READ, "Reading problem on writing mode");
    return cons_data[reading_pos++];
}

void Z3Problem::initCurrentMode() {
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
