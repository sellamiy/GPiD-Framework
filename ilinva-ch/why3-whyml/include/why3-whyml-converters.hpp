#ifndef WHY3_WHYML_ICH_FOR_GPID__CONVERTERS__HPP
#define WHY3_WHYML_ICH_FOR_GPID__CONVERTERS__HPP

#include <snlog/snlog.hpp>
#include <why3wrap/why3utils.hpp>

namespace gpid {

#if !defined SINGLE_SOLVER_ONLY || defined SINGLE_SOLVER_cvc4_tm_api

    template<> inline W3WML_Constraint convert<W3WML_ICH, CVC4InterfaceAPI, LiteralHypothesis>
    (ObjectMapper<CVC4InterfaceAPI::LiteralT> const& mapper, LiteralHypothesis& hyp,
     CVC4InterfaceAPI::ContextManagerT& ctx) {
        std::stringstream ss;
        ss << hypothesis<CVC4InterfaceAPI>(hyp, mapper, ctx);
        return W3WML_Constraint(why3wrap::Smt2Why3(ss.str()));
    }

    template<> CVC4InterfaceAPI::LiteralT convert<W3WML_ICH, CVC4InterfaceAPI>
    (const W3WML_Constraint&, CVC4InterfaceAPI::ContextManagerT&) {
        snlog::l_warn() << "Not implemented: " << __FILE__ << " : " << __LINE__ << snlog::l_end;
    }

#endif

#if !defined SINGLE_SOLVER_ONLY || defined SINGLE_SOLVER_cvc4_tm_smtl2_tm_cli

    template<> inline W3WML_Constraint convert<W3WML_ICH, CVC4InterfaceSMTl2CLI, LiteralHypothesis>
    (ObjectMapper<CVC4InterfaceSMTl2CLI::LiteralT> const& mapper, LiteralHypothesis& hyp,
     CVC4InterfaceSMTl2CLI::ContextManagerT& ctx) {
        std::stringstream ss;
        ss << hypothesis<CVC4InterfaceSMTl2CLI>(hyp, mapper, ctx);
        return W3WML_Constraint(why3wrap::Smt2Why3(ss.str()));
    }

    template<> CVC4InterfaceSMTl2CLI::LiteralT convert<W3WML_ICH, CVC4InterfaceSMTl2CLI>
    (const W3WML_Constraint& cons, CVC4InterfaceSMTl2CLI::ContextManagerT& ctx) {
        const std::string _cdata = cons;
        return SMTl2SolverLiteral(ctx.memory.alloc(_cdata));
    }

#endif

#if !defined SINGLE_SOLVER_ONLY || defined SINGLE_SOLVER_z3_tm_api

    template<> inline W3WML_Constraint convert<W3WML_ICH, Z3InterfaceAPI, LiteralHypothesis>
    (ObjectMapper<Z3InterfaceAPI::LiteralT> const& mapper, LiteralHypothesis& hyp,
     Z3InterfaceAPI::ContextManagerT& ctx) {
        std::stringstream ss;
        ss << hypothesis<Z3InterfaceAPI>(hyp, mapper, ctx);
        return W3WML_Constraint(why3wrap::Smt2Why3(ss.str()));
    }

    template<> Z3InterfaceAPI::LiteralT convert<W3WML_ICH, Z3InterfaceAPI>
    (const W3WML_Constraint& cons, Z3InterfaceAPI::ContextManagerT& ctx) {
        const std::string _cdata = cons;
        z3::expr z3d = ctx.parse_string(_cdata.c_str());
        return Z3Literal(z3d);
    }

#endif

#if !defined SINGLE_SOLVER_ONLY || defined SINGLE_SOLVER_z3_tm_smtl2_tm_cli

    template<> inline W3WML_Constraint convert<W3WML_ICH, Z3InterfaceSMTl2CLI, LiteralHypothesis>
    (ObjectMapper<Z3InterfaceSMTl2CLI::LiteralT> const& mapper, LiteralHypothesis& hyp,
     Z3InterfaceSMTl2CLI::ContextManagerT& ctx) {
        std::stringstream ss;
        ss << hypothesis<Z3InterfaceSMTl2CLI>(hyp, mapper, ctx);
        return W3WML_Constraint(why3wrap::Smt2Why3(ss.str()));
    }

    template<> Z3InterfaceSMTl2CLI::LiteralT convert<W3WML_ICH, Z3InterfaceSMTl2CLI>
    (const W3WML_Constraint& cons, Z3InterfaceSMTl2CLI::ContextManagerT& ctx) {
        const std::string _cdata = cons;
        return SMTl2SolverLiteral(ctx.memory.alloc(_cdata));
    }

#endif

}

#endif
