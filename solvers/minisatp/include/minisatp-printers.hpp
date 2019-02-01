#ifndef MINISAT_PATCHED_PRINTERS_FOR_GPID__HPP
#define MINISAT_PATCHED_PRINTERS_FOR_GPID__HPP

#include <vector>
#include <iostream>
#include <minisat/simp/SimpSolver.h>

extern inline std::ostream& operator<<(std::ostream& out, const std::vector<MinisatLiteral>& c) {
    out << "< ";
    for (MinisatLiteral hyp : c) out << hyp.lit << " ";
    return out << ">";
}

extern inline
void p_implicate(std::ostream& out, std::vector<MinisatLiteral>& impl, bool negate) {
    out << "> ";
    for (MinisatLiteral hyp : impl) out << (negate ? ~(hyp.lit) : hyp.lit) << " ";
    out << std::endl;
}

#endif
