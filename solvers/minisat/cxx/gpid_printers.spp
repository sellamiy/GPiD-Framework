#ifndef GPID_MINISAT_GPID_PRINTERS_SPP
#define GPID_MINISAT_GPID_PRINTERS_SPP

#include <iostream>

namespace gpid {

    extern inline std::ostream& operator<<(std::ostream& out, const std::vector<MinisatHypothesis>& c) {
        out << "< ";
        for (MinisatHypothesis hyp : c) out << hyp.lit << " ";
        return out << ">";
    }

    extern inline
    void p_implicate(std::ostream& out, std::vector<MinisatHypothesis>& impl, bool negate) {
        out << "> ";
        for (MinisatHypothesis hyp : impl) out << (negate ? ~(hyp.lit) : hyp.lit) << " ";
        out << std::endl;
    }

}

#endif
