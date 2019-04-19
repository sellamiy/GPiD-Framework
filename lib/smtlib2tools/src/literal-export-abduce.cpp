#define LIB_SMTLIB2_CPP_TOOLS__EXPORT__ABDUCE__CPP

#include <snlog/snlog.hpp>
#include <smtlib2tools/literal-presets.hpp>

using namespace smtlib2;

template<>
void smtlib2::dump<ExportPreset::Abduce>(const GenerationSet& gset, std::ostream& out) {
    out << "(size auto)" << std::endl;
    for (const smtlit_t& lit : gset.get_literals())
        out << "(abduce " << ident(lit) << ")" << std::endl;
}
