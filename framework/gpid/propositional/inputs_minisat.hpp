#ifndef GPID_MINISAT_INPUT_HANDLING_HPP
#define GPID_MINISAT_INPUT_HANDLING_HPP

#include <gpid/propositional/pengine_minisat.hpp>

namespace gpid {

    extern void parse_DIMACS(gzFile input_stream, MinisatProblem& P, bool strictp = false);

};

#endif
