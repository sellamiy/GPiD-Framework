#ifndef GPID_TRUESOLVER_CONTEXT_SPP
#define GPID_TRUESOLVER_CONTEXT_SPP

namespace gpid {

    struct ts__ctxm  { };
    struct ts__decls { };
    struct ts__hy    { };
    struct ts__mdl   {
        inline bool isSkippable (ts__hy&) const { return false; }
    };

}

#endif