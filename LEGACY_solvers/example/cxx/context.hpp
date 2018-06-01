#ifndef GPID_TRUESOLVER_CONTEXT_SPP
#define GPID_TRUESOLVER_CONTEXT_SPP

#include <ostream>

namespace gpid {

    struct ts__ctxm  { };
    struct ts__decls { };
    struct ts__lit    {
        inline const std::string str() const { return ""; }
    };
    struct ts__mdl   {
        inline bool isSkippable (ts__lit&) const { return false; }
    };

}

#endif
