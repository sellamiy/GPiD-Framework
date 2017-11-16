#ifndef GPID_CVC4_INPUT_HANDLING_HPP
#define GPID_CVC4_INPUT_HANDLING_HPP

#include <gpid/options/options_abducibles.hpp>
#include <gpid/solvers-wrap/cvc4_engine.hpp>

namespace gpid {

    extern void parse_file(std::string filename, CVC4::ExprManager& em, CVC4Problem& pbl,
                           std::string language);

    extern uint32_t countAbducibles(AbduciblesOptions& opts, CVC4Problem& pbl);
    extern void generateAbducibles
    (AbduciblesOptions& opts, CVC4::ExprManager& em, CVC4Declarations& decls, CVC4HypothesesSet& hys);

};

#endif
