#define CVC4_API_INTERFACE_FOR_GPID__INTERFACE_HANDLERS__CPP

#include <cvc4-api-interface.hpp>

gpid::CVC4InterfaceAPI::CVC4InterfaceAPI(CVC4::ExprManager& ctx)
    : ctx(ctx), solver(&ctx), iw_mdl(solver)
{
    solver.setOption("incremental", true);
    solver.setOption("produce-models", true);
    solver.setLogic("QF_ALL_SUPPORTED");
}
