#ifndef GPID_MINISAT_OUTPUT_HANDLING_HPP
#define GPID_MINISAT_OUTPUT_HANDLING_HPP

#include <iostream>
#include <gpid/config.hpp>
#include <gpid/propositional/minisat_pengine.hpp>

#ifdef MERGE_MINISAT_OUTPUT_WRAPPERS
namespace Minisat {
#else
namespace gpid {
#endif

    extern inline std::ostream& operator<<(std::ostream& out, const Minisat::Lit p) {
        return out << (p == Minisat::lit_Undef ? "?" : (p.x % 2 == 0 ? "" : "-")) << p.x/2 + 1;
    }

};

#endif
