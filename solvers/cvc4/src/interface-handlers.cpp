#define CVC4_API_INTERFACE_FOR_GPID__INTERFACE_HANDLERS__CPP

#include <cvc4-api-interface.hpp>

using namespace abdulot;

CVC4InterfaceAPI::CVC4InterfaceAPI(CVC4::ExprManager& ctx, const SolverInterfaceOptions& siopts)
    : ctx(ctx), siopts(siopts), solver(&ctx), iw_mdl(solver)
{
    solver.setOption("incremental", true);
    solver.setOption("produce-models", true);
    solver.setLogic("ALL_SUPPORTED");
}
