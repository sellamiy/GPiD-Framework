#define LIB_SMTLIB2_CPP_TOOLS__EXPORT__RAW__CPP

#include <snlog/snlog.hpp>
#include <smtlib2tools/literal-presets.hpp>

using namespace smtlib2;

template<>
void smtlib2::dump<ExportPreset::Raw>(const GenerationSet& gset, std::ostream& out) {
    out << "# Smtliterals generation dump" << std::endl;
    for (const smtlit_t& lit : gset.get_literals())
        out << ident(lit) << " (" << type(lit) << ")" << std::endl;
    out << "# Dump end" << std::endl;
}

