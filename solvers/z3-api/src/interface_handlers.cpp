#define Z3_API_INTERFACE_FOR_GPID__INTERFACE_HANDLERS__CPP

#include <z3-api-interface.hpp>

using namespace abdulot;

gpid::Z3InterfaceAPI::Z3InterfaceAPI(z3::context& ctx, const SolverInterfaceOptions& siopts)
    : ctx(ctx), siopts(siopts), solver(ctx), iw_mdl(solver)
{}
