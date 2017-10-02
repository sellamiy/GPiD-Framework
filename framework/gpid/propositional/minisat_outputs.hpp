#ifndef GPID_MINISAT_OUTPUT_HANDLING_HPP
#define GPID_MINISAT_OUTPUT_HANDLING_HPP

#include <gpid/propositional/minisat_pengine.hpp>

namespace gpid {

    extern void parse_DIMACS(gzFile input_stream, MinisatProblem& P, bool strictp = false);

};

#endif
