#ifndef GPID_CVC4_PROBLEM_SRC_SPP
#define GPID_CVC4_PROBLEM_SRC_SPP

#include <snlog/snlog.hpp>

namespace gpid {

    class CVC4ProblemInternal {
    public:
        std::vector<CVC4::Expr> cons_data;
        uint32_t reading_pos = -1;

        inline bool hasMoreConstraints() {
            return reading_pos < cons_data.size();
        }

        inline CVC4::Expr nextConstraint() {
            return cons_data[reading_pos++];
        }
    };

}

using namespace snlog;
using namespace gpid;

CVC4Problem::CVC4Problem(CVC4::ExprManager& ctx)
    : handler(new Internal()), ctx(ctx) { }

CVC4Problem::~CVC4Problem() { }

void CVC4Problem::addConstraint(CVC4::Expr cons) {
    t_warn(mode != IOMode::IO_WRITE, "Writing problem on reading mode");
    handler->cons_data.push_back(cons);
}

bool CVC4Problem::hasMoreConstraints() {
    t_warn(mode != IOMode::IO_READ, "Reading problem on writing mode");
    return handler->hasMoreConstraints();
}

CVC4::Expr CVC4Problem::nextConstraint() {
    t_warn(mode != IOMode::IO_READ, "Reading problem on writing mode");
    return handler->nextConstraint();
}

void CVC4Problem::initCurrentMode() {
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
