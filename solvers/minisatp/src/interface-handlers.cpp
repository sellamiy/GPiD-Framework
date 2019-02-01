#define MINISAT_PATCHED_INTERFACE_FOR_GPID__INTERFACE_HANDLERS__CPP

#include <minisatp-interface.hpp>

using namespace abdulot;

MinisatInterface::MinisatInterface(MinisatContextManager& ctx, const SolverInterfaceOptions& siopts)
    : ctx(ctx), siopts(siopts), iw_mdl(solver.model)
{
    solver.eliminate(true);
    solver.verbosity = 0;
    for (int i = 0; i < ctx.nVars; i++) {
        solver.newVar();
    }
}
