#define LIB_SMTLIB2_LITERAL_TOOLS__EXPORT__ABDUCE__CPP

#include <snlog/snlog.hpp>
#include <smtlit/smtlit-presets.hpp>

using namespace smtlit;

template<>
void smtlit::dump<ExportPreset::Abduce>(const GenerationSet& gset, std::ostream& out) {
    out << "(size auto)" << std::endl;
    for (const smtlit_t& lit : gset.get_literals())
        out << "(abduce " << ident(lit) << ")" << std::endl;
}
