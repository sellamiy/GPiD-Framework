#ifndef GPID_Z3_INPUT_HANDLING_HPP
#define GPID_Z3_INPUT_HANDLING_HPP

#include <gpid/options/options_abducibles.hpp>
#include <gpid/smt/z3_engine.hpp>

namespace gpid {

    extern void parse_Z(const std::string& filename, z3::context& ctx, Z3Problem& pbl);

    extern uint32_t countAbducibles(AbduciblesOptions& opts, Z3Problem& pbl);
    extern void generateAbducibles
    (AbduciblesOptions& opts, z3::context& ctx, Z3Declarations& decls, Z3HypothesesSet& hys);

};

#endif
