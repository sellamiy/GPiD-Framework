#ifndef GPID_Z3_INPUT_HANDLING_HPP
#define GPID_Z3_INPUT_HANDLING_HPP

#include <gpid/options/options_abducibles.hpp>
#include <gpid/smt/z3_engine.hpp>

namespace gpid {

    extern void parse_file(std::string filename, Z3Problem& pbl, std::string language);

    extern uint32_t countAbducibles(AbduciblesOptions& opts, Z3Problem& pbl);
    extern void generateAbducibles
    (AbduciblesOptions& opts, z3::context& ctx, Z3Declarations& decls, Z3HypothesesSet& hys);

};

#endif
