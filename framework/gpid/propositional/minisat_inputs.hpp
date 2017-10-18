#ifndef GPID_MINISAT_INPUT_HANDLING_HPP
#define GPID_MINISAT_INPUT_HANDLING_HPP

#include <gpid/options/options_abducibles.hpp>
#include <gpid/propositional/minisat_pengine.hpp>

namespace gpid {

    extern void parse_DIMACS(gzFile input_stream, MinisatProblem& P, bool strictp = false);

    extern uint32_t countAbducibles(AbduciblesOptions& opts, MinisatProblem& pbl);
    extern void generateAbducibles(AbduciblesOptions& opts, MinisatHypothesesSet& hys, int nVars);

};

#endif
