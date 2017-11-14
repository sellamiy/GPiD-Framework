#ifndef GPID_MINISAT_INPUT_HANDLING_HPP
#define GPID_MINISAT_INPUT_HANDLING_HPP

#include <gpid/options/options_abducibles.hpp>
#include <gpid/propositional/minisat_engine.hpp>

namespace gpid {

    extern void parse_file(std::string filename, MinisatProblem& P, std::string language);

    extern uint32_t countAbducibles(AbduciblesOptions& opts, MinisatProblem& pbl);
    extern void generateAbducibles(AbduciblesOptions& opts, MinisatHypothesesSet& hys, int nVars);

};

#endif
