#ifndef LIB_SMTLIB2_LITERAL_TOOLS__PRESETS__HEADER
#define LIB_SMTLIB2_LITERAL_TOOLS__PRESETS__HEADER

#include <set>
#include <string>
#include <memory>
#include <smtlit/smtlit-fabricator.hpp>

namespace smtlit {

    class GenerationSet {
        std::shared_ptr<SmtLitFabricator> fabricator;
    public:
        GenerationSet() : fabricator(new SmtLitFabricator()) {}
        GenerationSet(const GenerationSet& o) : fabricator(o.fabricator) {}
        inline SmtLitFabricator& get_fabricator() { return *fabricator; }
        inline const std::set<smtlit_t>& get_literals() const
        { return fabricator->get_filtered(); }
    };

    enum class GenerationSource { File, Raw };
    enum class GenerationPreset { SMTlib2, Mlb, WhyML };

    template<GenerationSource Source, GenerationPreset Preset>
    const GenerationSet generate_literals(const std::string& source);

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

    enum class ExportPreset { Raw, Abduce };

    template<ExportPreset Preset>
    void dump(const GenerationSet& gset, std::ostream& out);

    template<> void dump<ExportPreset::Raw>(const GenerationSet& gset, std::ostream& out);
    template<> void dump<ExportPreset::Abduce>(const GenerationSet& gset, std::ostream& out);
}

#endif
