#ifndef GPID_CVC4_INTERFACE_SRC_SPP
#define GPID_CVC4_INTERFACE_SRC_SPP

using namespace gpid;

CVC4SolverInterface::CVC4SolverInterface(CVC4::ExprManager& ctx)
    : AbstractSolverInterface(ctx), _internal(new CVC4SolverInternal(&ctx)) {}

#endif
