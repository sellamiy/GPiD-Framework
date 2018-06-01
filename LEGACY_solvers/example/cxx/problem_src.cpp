#ifndef GPID_TRUESOLVER_PROBLEM_SRC_SPP
#define GPID_TRUESOLVER_PROBLEM_SRC_SPP

namespace gpid {

    class ts__pblInternal { };

    ts__pbl::ts__pbl (ts__ctxm& ctx) : handler(new ts__pblInternal()), ctx(ctx) { }
    ts__pbl::~ts__pbl()                                                         { }

}

#endif
