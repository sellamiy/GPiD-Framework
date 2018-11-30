#ifndef LIB_SMTLIB2_CPP_TOOLS__LITERALS_GENERATION_PRESETS__HEADER
#define LIB_SMTLIB2_CPP_TOOLS__LITERALS_GENERATION_PRESETS__HEADER

#include <smtlib2tools/smtlit-generation.hpp>

namespace smtlib2 {

    template<> const GenerationSet
    generate_literals<GenerationSource::File, GenerationPreset::SMTlib2>(const std::string& filename);
    template<> const GenerationSet
    generate_literals<GenerationSource::Raw, GenerationPreset::SMTlib2>(const std::string& data);

    template<> const GenerationSet
    generate_literals<GenerationSource::File, GenerationPreset::Mlb>(const std::string& filename);
    template<> const GenerationSet
    generate_literals<GenerationSource::Raw, GenerationPreset::Mlb>(const std::string& data);

    template<> const GenerationSet
    generate_literals<GenerationSource::File, GenerationPreset::WhyML>(const std::string& filename);
    template<> const GenerationSet
    generate_literals<GenerationSource::Raw, GenerationPreset::WhyML>(const std::string& data);

    template<> void dump<ExportPreset::Raw>(const GenerationSet& gset, std::ostream& out);
    template<> void dump<ExportPreset::Abduce>(const GenerationSet& gset, std::ostream& out);

}

#endif
