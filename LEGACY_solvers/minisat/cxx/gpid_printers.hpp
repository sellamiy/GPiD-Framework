#ifndef GPID_MINISAT_GPID_PRINTERS_SPP
#define GPID_MINISAT_GPID_PRINTERS_SPP

#include <iostream>

namespace gpid {

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

    template<> inline std::ostream& operator<< <MinisatLiteral>
    (std::ostream& out, const LiteralHypothesisPrinter<MinisatLiteral>& hlp) {
        for (auto lit : hlp.hypothesis) {
            Minisat::Lit mlit = hlp.mapper.get(lit).lit;
            out << " " << (hlp.negate ? ~mlit : mlit);
        }
        return out;
    }

}

#endif
