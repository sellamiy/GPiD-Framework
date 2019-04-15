/**
 * \file smtlib2tools/smtlit-generation.hpp
 * \brief Literal generation core.
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_SMTLIB2_CPP_TOOLS__LITERALS_GENERATION__HEADER
#define LIB_SMTLIB2_CPP_TOOLS__LITERALS_GENERATION__HEADER

#include <memory>
#include <smtlib2tools/smtlit-fabricator.hpp>

namespace smtlib2 {

    class GenerationSet {
        std::shared_ptr<SmtLitFabricator> fabricator;
    public:
        GenerationSet() : fabricator(new SmtLitFabricator()) {}
        GenerationSet(const GenerationSet& o) : fabricator(o.fabricator) {}
        inline SmtLitFabricator& get_fabricator() { return *fabricator; }
        inline const std::set<smtlit_t>& get_literals() const
        { return fabricator->get_filtered(); }
        inline const std::set<smtident_t>& get_annotated(const smtannotation_t& annot) const
        { return fabricator->get_annotated(annot); }
    };

    enum class GenerationSource { File, Raw };
    enum class GenerationPreset { SMTlib2, Mlb };

    template<GenerationSource Source, GenerationPreset Preset>
    const GenerationSet generate_literals(const std::string& source);

    enum class ExportPreset { Raw, Abduce };

    template<ExportPreset Preset>
    void dump(const GenerationSet& gset, std::ostream& out);

}

#endif
