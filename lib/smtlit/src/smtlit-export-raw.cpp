#define LIB_SMTLIB2_LITERAL_TOOLS__EXPORT__RAW__CPP

#include <snlog/snlog.hpp>
#include <smtlit/smtlit-presets.hpp>

using namespace smtlit;

template<>
void smtlit::dump<ExportPreset::Raw>(const GenerationSet& gset, std::ostream& out) {
    out << "# Smtliterals generation dump" << std::endl;
    for (const smtlit_t& lit : gset.get_literals())
        out << ident(lit) << " (" << type(lit) << ")" << std::endl;
    out << "# Dump end" << std::endl;
}

