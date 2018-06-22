#define Z3_API_INTERFACE_FOR_GPID__INTERFACE_HANDLERS__CPP

#include <z3-api-interface.hpp>

gpid::Z3InterfaceAPI::Z3InterfaceAPI(z3::context& ctx)
    : ctx(ctx), solver(ctx), iw_mdl(solver)
{}
