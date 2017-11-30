#ifndef GPID_Z3_PROBLEM_SRC_SPP
#define GPID_Z3_PROBLEM_SRC_SPP

#include <snlog/snlog.hpp>

namespace gpid {

    class Z3ProblemInternal {
    public:
        std::vector<z3::expr> cons_data;
        uint32_t reading_pos = -1;

        inline bool hasMoreConstraints() {
            return reading_pos < cons_data.size();
        }

        inline z3::expr nextConstraint() {
            return cons_data[reading_pos++];
        }
    };

}

using namespace snlog;
using namespace gpid;

Z3Problem::Z3Problem(z3::context& ctx)
    : handler(new Internal()), ctx(ctx), decls(ctx) { }

Z3Problem::~Z3Problem() { }

void Z3Problem::addConstraint(z3::expr cons) {
    t_warn(mode != IOMode::IO_WRITE, "Writing problem on reading mode");
    handler->cons_data.push_back(cons);
    decls.collect(ctx, cons);
}

bool Z3Problem::hasMoreConstraints() {
    t_warn(mode != IOMode::IO_READ, "Reading problem on writing mode");
    return handler->hasMoreConstraints();
}

z3::expr Z3Problem::nextConstraint() {
    t_warn(mode != IOMode::IO_READ, "Reading problem on writing mode");
    return handler->nextConstraint();
}

void Z3Problem::initCurrentMode() {
    switch (mode) {
    case IO_READ:
        handler->reading_pos = 0;
        break;
    case IO_WRITE:
        handler->reading_pos = -1;
        break;
    default:
        // TODO: Raise Error
        l_internal("Minisat problem ended in an Unknown state!");
        break;
    }
}

#endif
