#define LIB_SMTLIB2_CPP_TOOLS__PRESET__WHYML__CPP

#include <fstream>
#include <sstream>
#include <snlog/snlog.hpp>
#include <ugly/ugly.hpp>
#include <whymlp/whymlp.hpp>
#include <smtlib2tools/smtlib2-annotations.hpp>
#include <smtlib2tools/smtlib2-types.hpp>
#include <smtlib2tools/smtlib2-functions.hpp>
#include <smtlib2tools/parser-command.hpp>
#include <smtlib2tools/parser-tokens.hpp>
#include <smtlib2tools/smtlit-presets.hpp>

using namespace smtlib2;

static const smttype_t from_whyml_type(const std::string& whymlt) {
    if (whymlt == "int") return smt_int;
    if (whymlt == "real") return smt_real;
    if (whymlt == "bool") return smt_bool;
    return whymlt;
}

static void loc_fabricate(SmtLitFabricator& fabricator, whymlp::ExtractorParser& parser) {
    const FabricationFilter coreConstFilter(FilterPolicy::Annotation_Include, annot_core_const);
    const FabricationFilter coreMagicFilter(FilterPolicy::Annotation_Include, annot_core_magic);
    if (ugly::mapHasValue<std::string, std::string>(parser.getVars(), "bool")) {
        FabricationRule _f0
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_not_f, annot_applied);
        _f0.add_filter(coreConstFilter);
        _f0.add_filter(coreMagicFilter);
        FabricationRule _f1
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_eq_f("Bool"), annot_applied);
        _f1.add_filter(coreConstFilter);
        _f1.add_filter(coreMagicFilter);
        FabricationRule _f2
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_neq_f("Bool"), annot_applied);
        _f2.add_filter(coreConstFilter);
        _f2.add_filter(coreMagicFilter);
        fabricator.fabricate(_f0);
        fabricator.fabricate(_f1);
        fabricator.fabricate(_f2);
    }
    if (ugly::mapHasValue<std::string, std::string>(parser.getVars(), "int")) {
        FabricationRule _f0
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_eq_f("Int"), annot_applied);
        _f0.add_filter(coreConstFilter);
        _f0.add_filter(coreMagicFilter);
        FabricationRule _f1
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_neq_f("Int"), annot_applied);
        _f1.add_filter(coreConstFilter);
        _f1.add_filter(coreMagicFilter);
        FabricationRule _f2
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_leq_f("Int"), annot_applied);
        _f2.add_filter(coreConstFilter);
        _f2.add_filter(coreMagicFilter);
        FabricationRule _f3
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_geq_f("Int"), annot_applied);
        _f3.add_filter(coreConstFilter);
        _f3.add_filter(coreMagicFilter);
        FabricationRule _f4
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_lt_f("Int"), annot_applied);
        _f4.add_filter(coreConstFilter);
        _f4.add_filter(coreMagicFilter);
        FabricationRule _f5
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_gt_f("Int"), annot_applied);
        _f5.add_filter(coreConstFilter);
        _f5.add_filter(coreMagicFilter);
        fabricator.fabricate(_f0);
        fabricator.fabricate(_f1);
        fabricator.fabricate(_f2);
        fabricator.fabricate(_f3);
        fabricator.fabricate(_f4);
        fabricator.fabricate(_f5);
    }
}

template<typename SourceT>
static const GenerationSet loc_generate(const SourceT& source) {
    GenerationSet result;
    SmtLitFabricator& fabricator = result.get_fabricator();
    whymlp::ExtractorParser parser(source);
    for (const std::pair<std::string, std::string>& v : parser.getVars()) {
        fabricator.insert(smtlit_t(v.first, from_whyml_type(v.second)), annot_core_const);
    }
    for (const std::pair<std::string, std::string>& l : parser.getLits()) {
        fabricator.insert(smtlit_t(l.first, from_whyml_type(l.second)), annot_core_magic);
    }
    for (const std::string& ident : parser.getRefs()) {
        fabricator.annotate(ident, annot_whyml_ref);
    }
    loc_fabricate(fabricator, parser);
    FiltrationRule bool_filter(FilterMode::Conjunctive);
    bool_filter.add_filter(FabricationFilter(FilterPolicy::Type_Include, smt_bool));
    fabricator.filter(bool_filter, true);
    return result;
}

template<> const GenerationSet
smtlib2::generate_literals<GenerationSource::File, GenerationPreset::WhyML>(const std::string& filename) {
    // Wrap through the smtlib2utils file interface
    return loc_generate<std::string>(filename);
}

template<> const GenerationSet
smtlib2::generate_literals<GenerationSource::Raw, GenerationPreset::WhyML>(const std::string&) {
    // This wrap does not exist
    snlog::l_error() << "String-data generation flow for WhyML does not exist" << snlog::l_end
                     << snlog::l_error << "Please use files" << snlog::l_end;
    GenerationSet _dum;
    return _dum;
}
