#ifndef WHY3_WHYML_IPH_FOR_GPID__CONVERTERS__HPP
#define WHY3_WHYML_IPH_FOR_GPID__CONVERTERS__HPP

#include <why3cpp/why3utils.hpp>
#include <abdulot/ilinva/data-dual.hpp>
#include <abdulot/saihelpers/smtlib2.hpp>

namespace abdulot {
namespace ilinva {

template<typename InterfaceT, typename LiteralHypothesisT>
inline Why3_Constraint convert_w3wml
(abdulot::ObjectMapper<typename InterfaceT::LiteralT> const& mapper,
 LiteralHypothesisT& hyp, typename InterfaceT::ContextManagerT& ctx) {
    std::stringstream ss;
    ss << abdulot::hypothesis<InterfaceT>(hyp, mapper, ctx);
    return Why3_Constraint(ss.str());
}

using LiteralHypothesis = abdulot::gpid::LiteralHypothesis;
using GunitiHypothesis = abdulot::gpid::GunitiHypothesis;

/*
#if defined SOLVER_INTERFACE_lcvc4

// TODO: Add parameter in template for passing why3 refs for these converters
// TODO: Something like IPHContextManager (?)

template<> inline Why3_Constraint
convert<Why3_IPH, CVC4InterfaceAPI, LiteralHypothesis>
(abdulot::ObjectMapper<CVC4InterfaceAPI::LiteralT> const& mapper, LiteralHypothesis& hyp,
 CVC4InterfaceAPI::ContextManagerT& ctx) {
    return convert_w3wml<CVC4InterfaceAPI, LiteralHypothesis>(mapper, hyp, ctx);
}

template<> inline Why3_Constraint
convert<Why3_IPH, CVC4InterfaceAPI, GunitiHypothesis>
(abdulot::ObjectMapper<CVC4InterfaceAPI::LiteralT> const& mapper, GunitiHypothesis& hyp,
 CVC4InterfaceAPI::ContextManagerT& ctx) {
    return convert_w3wml<CVC4InterfaceAPI, GunitiHypothesis>(mapper, hyp, ctx);
}

template<> CVC4InterfaceAPI::LiteralT
convert<Why3_IPH, CVC4InterfaceAPI>
(const Why3_Constraint&, CVC4InterfaceAPI::ContextManagerT&) {
    snlog::l_warn() << "Not implemented: " << __FILE__ << " : " << __LINE__ << snlog::l_end;
}

#endif
*/

#if defined SOLVER_INTERFACE_ccvc4

template<> inline Why3_Constraint
convert<Why3_IPH, CVC4InterfaceSMTl2CLI, LiteralHypothesis>
(abdulot::ObjectMapper<CVC4InterfaceSMTl2CLI::LiteralT> const& mapper, LiteralHypothesis& hyp,
 CVC4InterfaceSMTl2CLI::ContextManagerT& ctx) {
    return convert_w3wml<CVC4InterfaceSMTl2CLI, LiteralHypothesis>(mapper, hyp, ctx);
}

template<> inline Why3_Constraint
convert<Why3_IPH, CVC4InterfaceSMTl2CLI, GunitiHypothesis>
(abdulot::ObjectMapper<CVC4InterfaceSMTl2CLI::LiteralT> const& mapper, GunitiHypothesis& hyp,
 CVC4InterfaceSMTl2CLI::ContextManagerT& ctx) {
    return convert_w3wml<CVC4InterfaceSMTl2CLI, GunitiHypothesis>(mapper, hyp, ctx);
}

template<> CVC4InterfaceSMTl2CLI::LiteralT
convert<Why3_IPH, CVC4InterfaceSMTl2CLI>
(const Why3_Constraint& cons, CVC4InterfaceSMTl2CLI::ContextManagerT& ctx) {
    const std::string _cdata = cons;
    return abdulot::saihelpers::SMTl2SolverLiteral(ctx.memory.alloc(_cdata));
}

#endif

/*
#if defined SOLVER_INTERFACE_lz3

template<> inline Why3_Constraint
convert<Why3_IPH, Z3InterfaceAPI, LiteralHypothesis>
(abdulot::ObjectMapper<Z3InterfaceAPI::LiteralT> const& mapper, LiteralHypothesis& hyp,
 Z3InterfaceAPI::ContextManagerT& ctx) {
    return convert_w3wml<Z3InterfaceAPI, LiteralHypothesis>(mapper, hyp, ctx);
}

template<> inline Why3_Constraint
convert<Why3_IPH, Z3InterfaceAPI, GunitiHypothesis>
(abdulot::ObjectMapper<Z3InterfaceAPI::LiteralT> const& mapper, GunitiHypothesis& hyp,
 Z3InterfaceAPI::ContextManagerT& ctx) {
    return convert_w3wml<Z3InterfaceAPI, GunitiHypothesis>(mapper, hyp, ctx);
}

template<> Z3InterfaceAPI::LiteralT
convert<Why3_IPH, Z3InterfaceAPI>
(const Why3_Constraint& cons, Z3InterfaceAPI::ContextManagerT& ctx) {
    const std::string _cdata = cons;
    z3::expr z3d = ctx.parse_string(_cdata.c_str());
    return Z3Literal(z3d);
}

#endif
*/

#if defined SOLVER_INTERFACE_cz3

template<> inline Why3_Constraint
convert<Why3_IPH, Z3InterfaceSMTl2CLI, LiteralHypothesis>
(abdulot::ObjectMapper<Z3InterfaceSMTl2CLI::LiteralT> const& mapper, LiteralHypothesis& hyp,
 Z3InterfaceSMTl2CLI::ContextManagerT& ctx) {
    return convert_w3wml<Z3InterfaceSMTl2CLI, LiteralHypothesis>(mapper, hyp, ctx);
}

template<> inline Why3_Constraint
convert<Why3_IPH, Z3InterfaceSMTl2CLI, GunitiHypothesis>
(abdulot::ObjectMapper<Z3InterfaceSMTl2CLI::LiteralT> const& mapper, GunitiHypothesis& hyp,
 Z3InterfaceSMTl2CLI::ContextManagerT& ctx) {
    return convert_w3wml<Z3InterfaceSMTl2CLI, GunitiHypothesis>(mapper, hyp, ctx);
}

template<> Z3InterfaceSMTl2CLI::LiteralT
convert<Why3_IPH, Z3InterfaceSMTl2CLI>
(const Why3_Constraint& cons, Z3InterfaceSMTl2CLI::ContextManagerT& ctx) {
    const std::string _cdata = cons;
    return abdulot::saihelpers::SMTl2SolverLiteral(ctx.memory.alloc(_cdata));
}

#endif

#if defined SOLVER_INTERFACE_saltergo

template<> inline Why3_Constraint
convert<Why3_IPH, AltErgoPSmt2Interface, LiteralHypothesis>
(abdulot::ObjectMapper<AltErgoPSmt2Interface::LiteralT> const& mapper, LiteralHypothesis& hyp,
 AltErgoPSmt2Interface::ContextManagerT& ctx) {
    return convert_w3wml<AltErgoPSmt2Interface, LiteralHypothesis>(mapper, hyp, ctx);
}

template<> inline Why3_Constraint
convert<Why3_IPH, AltErgoPSmt2Interface, GunitiHypothesis>
(abdulot::ObjectMapper<AltErgoPSmt2Interface::LiteralT> const& mapper, GunitiHypothesis& hyp,
 AltErgoPSmt2Interface::ContextManagerT& ctx) {
    return convert_w3wml<AltErgoPSmt2Interface, GunitiHypothesis>(mapper, hyp, ctx);
}

template<> AltErgoPSmt2Interface::LiteralT
convert<Why3_IPH, AltErgoPSmt2Interface>
(const Why3_Constraint& cons, AltErgoPSmt2Interface::ContextManagerT& ctx) {
    const std::string _cdata = cons;
    return abdulot::saihelpers::SMTl2SolverLiteral(ctx.memory.alloc(_cdata));
}

#endif

}
}

#endif
