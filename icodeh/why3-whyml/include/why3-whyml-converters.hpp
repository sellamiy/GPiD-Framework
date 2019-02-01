#ifndef WHY3_WHYML_ICH_FOR_GPID__CONVERTERS__HPP
#define WHY3_WHYML_ICH_FOR_GPID__CONVERTERS__HPP

#include <snlog/snlog.hpp>
#include <why3cpp/why3utils.hpp>
#include <abdulot/ilinva/data-dual.hpp>
#include <abdulot/saihelpers/smtlib2.hpp>

template<typename InterfaceT, typename LiteralHypothesisT>
inline W3WML_Constraint convert_w3wml
(abdulot::ObjectMapper<typename InterfaceT::LiteralT> const& mapper,
 LiteralHypothesisT& hyp, typename InterfaceT::ContextManagerT& ctx) {
    std::stringstream ss;
    ss << abdulot::hypothesis<InterfaceT>(hyp, mapper, ctx);
    return W3WML_Constraint(ss.str());
}

using LiteralHypothesis = abdulot::gpid::LiteralHypothesis;
using GunitiHypothesis = abdulot::gpid::GunitiHypothesis;

#if !defined SINGLE_SOLVER_ONLY || defined SINGLE_SOLVER_cvc4_tm_api

// TODO: Add parameter in template for passing why3 refs for these converters
// TODO: Something like ICHContextManager (?)

template<> inline W3WML_Constraint abdulot::ilinva::
convert<W3WML_ICH, CVC4InterfaceAPI, LiteralHypothesis>
(abdulot::ObjectMapper<CVC4InterfaceAPI::LiteralT> const& mapper, LiteralHypothesis& hyp,
 CVC4InterfaceAPI::ContextManagerT& ctx) {
    return convert_w3wml<CVC4InterfaceAPI, LiteralHypothesis>(mapper, hyp, ctx);
}

template<> inline W3WML_Constraint abdulot::ilinva::
convert<W3WML_ICH, CVC4InterfaceAPI, GunitiHypothesis>
(abdulot::ObjectMapper<CVC4InterfaceAPI::LiteralT> const& mapper, GunitiHypothesis& hyp,
 CVC4InterfaceAPI::ContextManagerT& ctx) {
    return convert_w3wml<CVC4InterfaceAPI, GunitiHypothesis>(mapper, hyp, ctx);
}

template<> CVC4InterfaceAPI::LiteralT abdulot::ilinva::
convert<W3WML_ICH, CVC4InterfaceAPI>
(const W3WML_Constraint&, CVC4InterfaceAPI::ContextManagerT&) {
    snlog::l_warn() << "Not implemented: " << __FILE__ << " : " << __LINE__ << snlog::l_end;
}

#endif

#if !defined SINGLE_SOLVER_ONLY || defined SINGLE_SOLVER_cvc4_tm_smtl2_tm_cli

template<> inline W3WML_Constraint abdulot::ilinva::
convert<W3WML_ICH, CVC4InterfaceSMTl2CLI, LiteralHypothesis>
(abdulot::ObjectMapper<CVC4InterfaceSMTl2CLI::LiteralT> const& mapper, LiteralHypothesis& hyp,
 CVC4InterfaceSMTl2CLI::ContextManagerT& ctx) {
    return convert_w3wml<CVC4InterfaceSMTl2CLI, LiteralHypothesis>(mapper, hyp, ctx);
}

template<> inline W3WML_Constraint abdulot::ilinva::
convert<W3WML_ICH, CVC4InterfaceSMTl2CLI, GunitiHypothesis>
(abdulot::ObjectMapper<CVC4InterfaceSMTl2CLI::LiteralT> const& mapper, GunitiHypothesis& hyp,
 CVC4InterfaceSMTl2CLI::ContextManagerT& ctx) {
    return convert_w3wml<CVC4InterfaceSMTl2CLI, GunitiHypothesis>(mapper, hyp, ctx);
}

template<> CVC4InterfaceSMTl2CLI::LiteralT abdulot::ilinva::
convert<W3WML_ICH, CVC4InterfaceSMTl2CLI>
(const W3WML_Constraint& cons, CVC4InterfaceSMTl2CLI::ContextManagerT& ctx) {
    const std::string _cdata = cons;
    return abdulot::saihelpers::SMTl2SolverLiteral(ctx.memory.alloc(_cdata));
}

#endif

#if !defined SINGLE_SOLVER_ONLY || defined SINGLE_SOLVER_z3_tm_api

template<> inline W3WML_Constraint abdulot::ilinva::
convert<W3WML_ICH, Z3InterfaceAPI, LiteralHypothesis>
(abdulot::ObjectMapper<Z3InterfaceAPI::LiteralT> const& mapper, LiteralHypothesis& hyp,
 Z3InterfaceAPI::ContextManagerT& ctx) {
    return convert_w3wml<Z3InterfaceAPI, LiteralHypothesis>(mapper, hyp, ctx);
}

template<> inline W3WML_Constraint abdulot::ilinva::
convert<W3WML_ICH, Z3InterfaceAPI, GunitiHypothesis>
(abdulot::ObjectMapper<Z3InterfaceAPI::LiteralT> const& mapper, GunitiHypothesis& hyp,
 Z3InterfaceAPI::ContextManagerT& ctx) {
    return convert_w3wml<Z3InterfaceAPI, GunitiHypothesis>(mapper, hyp, ctx);
}

template<> Z3InterfaceAPI::LiteralT abdulot::ilinva::
convert<W3WML_ICH, Z3InterfaceAPI>
(const W3WML_Constraint& cons, Z3InterfaceAPI::ContextManagerT& ctx) {
    const std::string _cdata = cons;
    z3::expr z3d = ctx.parse_string(_cdata.c_str());
    return Z3Literal(z3d);
}

#endif

#if !defined SINGLE_SOLVER_ONLY || defined SINGLE_SOLVER_z3_tm_smtl2_tm_cli

template<> inline W3WML_Constraint abdulot::ilinva::
convert<W3WML_ICH, Z3InterfaceSMTl2CLI, LiteralHypothesis>
(abdulot::ObjectMapper<Z3InterfaceSMTl2CLI::LiteralT> const& mapper, LiteralHypothesis& hyp,
 Z3InterfaceSMTl2CLI::ContextManagerT& ctx) {
    return convert_w3wml<Z3InterfaceSMTl2CLI, LiteralHypothesis>(mapper, hyp, ctx);
}

template<> inline W3WML_Constraint abdulot::ilinva::
convert<W3WML_ICH, Z3InterfaceSMTl2CLI, GunitiHypothesis>
(abdulot::ObjectMapper<Z3InterfaceSMTl2CLI::LiteralT> const& mapper, GunitiHypothesis& hyp,
 Z3InterfaceSMTl2CLI::ContextManagerT& ctx) {
    return convert_w3wml<Z3InterfaceSMTl2CLI, GunitiHypothesis>(mapper, hyp, ctx);
}

template<> Z3InterfaceSMTl2CLI::LiteralT abdulot::ilinva::
convert<W3WML_ICH, Z3InterfaceSMTl2CLI>
(const W3WML_Constraint& cons, Z3InterfaceSMTl2CLI::ContextManagerT& ctx) {
    const std::string _cdata = cons;
    return abdulot::saihelpers::SMTl2SolverLiteral(ctx.memory.alloc(_cdata));
}

#endif

#endif
