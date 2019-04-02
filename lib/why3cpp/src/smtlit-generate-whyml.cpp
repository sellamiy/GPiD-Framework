#define LIB_WHY3CPP__LITERALS_GENERATION_PRESET__FROM_WHYML__CPP

#include <fstream>
#include <sstream>
#include <snlog/snlog.hpp>
#include <ugly/ugly.hpp>
#include <smtlib2tools/smtlib2-functions.hpp>
#include <why3cpp/whyml-extractor.hpp>
#include <why3cpp/whyml-smtlit.hpp>

using namespace smtlib2;

static const smttype_t from_whyml_type(const std::string& whymlt) {
    if (whymlt == "int") return smt_int;
    if (whymlt == "real") return smt_real;
    if (whymlt == "bool") return smt_bool;
    return whymlt;
}

static void loc_fabricate(SmtLitFabricator& fabricator, why3cpp::ExtractorParser& parser) {
    const FabricationFilter coreConstFilter(FilterPolicy::Annotation_Include, annot_core_const);
    const FabricationFilter coreMagicFilter(FilterPolicy::Annotation_Include, annot_core_magic);
    const FabricationFilter PreparedFilter(FilterPolicy::Annotation_Include, annot_prepared);
    const FabricationFilter coreNAMgcFilter(FilterPolicy::Annotation_NotAll, annot_core_magic);
    const std::map<std::string, std::vector<std::vector<std::string>>>& papps = parser.getAppls();
    for (auto papp : papps) {
        if (papp.first == "+") {
            for (auto varapt : papp.second) {
                smtparam_binding_set _binds;
                _binds[0] = varapt.at(0);
                _binds[1] = varapt.at(1);
                FabricationRule _f(FilterMode::Conjunctive, FabricationPolicy::Apply_Symmetric,
                                   smt_plus_f(smt_int), _binds, annot_prepared);
                fabricator.fabricate(_f);
            }
        }
        if (papp.first == "*") {
            for (auto varapt : papp.second) {
                smtparam_binding_set _binds;
                _binds[0] = varapt.at(0);
                _binds[1] = varapt.at(1);
                FabricationRule _f(FilterMode::Conjunctive, FabricationPolicy::Apply_Symmetric,
                                   smt_mult_f(smt_int), _binds, annot_prepared);
                fabricator.fabricate(_f);
            }
        }
    }
    /* Fabricate boolean comparators */
    if (ugly::mapHasValue<std::string, std::string>(parser.getVars(), "bool")) {
        FabricationRule _f0
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Simple, smt_not_f, annot_applied);
        _f0.add_filter(coreConstFilter);
        _f0.add_filter(coreMagicFilter);
        _f0.add_filter(PreparedFilter);
        FabricationRule _f1
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Symmetric, smt_eq_f("Bool"), annot_applied);
        _f1.add_filter(coreConstFilter);
        _f1.add_filter(coreMagicFilter);
        _f1.add_filter(PreparedFilter);
        _f1.add_filter(coreNAMgcFilter);
        FabricationRule _f2
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Symmetric, smt_neq_f("Bool"), annot_applied);
        _f2.add_filter(coreConstFilter);
        _f2.add_filter(coreMagicFilter);
        _f2.add_filter(PreparedFilter);
        _f2.add_filter(coreNAMgcFilter);
        fabricator.fabricate(_f0);
        fabricator.fabricate(_f1);
        fabricator.fabricate(_f2);
    }
    /* Fabricate integer comparators */
    if (ugly::mapHasValue<std::string, std::string>(parser.getVars(), "int")) {
        FabricationRule _f0
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Symmetric, smt_eq_f("Int"), annot_applied);
        _f0.add_filter(coreConstFilter);
        _f0.add_filter(coreMagicFilter);
        _f0.add_filter(PreparedFilter);
        _f0.add_filter(coreNAMgcFilter);
        FabricationRule _f1
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Symmetric, smt_neq_f("Int"), annot_applied);
        _f1.add_filter(coreConstFilter);
        _f1.add_filter(coreMagicFilter);
        _f1.add_filter(PreparedFilter);
        _f1.add_filter(coreNAMgcFilter);
        FabricationRule _f2
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Symmetric, smt_leq_f("Int"), annot_applied);
        _f2.add_filter(coreConstFilter);
        _f2.add_filter(coreMagicFilter);
        _f2.add_filter(PreparedFilter);
        _f2.add_filter(coreNAMgcFilter);
        FabricationRule _f3
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Symmetric, smt_geq_f("Int"), annot_applied);
        _f3.add_filter(coreConstFilter);
        _f3.add_filter(coreMagicFilter);
        _f3.add_filter(PreparedFilter);
        _f3.add_filter(coreNAMgcFilter);
        FabricationRule _f4
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Symmetric, smt_lt_f("Int"), annot_applied);
        _f4.add_filter(coreConstFilter);
        _f4.add_filter(coreMagicFilter);
        _f4.add_filter(PreparedFilter);
        _f4.add_filter(coreNAMgcFilter);
        FabricationRule _f5
            (FilterMode::Disjunctive, FabricationPolicy::Apply_Symmetric, smt_gt_f("Int"), annot_applied);
        _f5.add_filter(coreConstFilter);
        _f5.add_filter(coreMagicFilter);
        _f5.add_filter(PreparedFilter);
        _f5.add_filter(coreNAMgcFilter);
        fabricator.fabricate(_f0);
        fabricator.fabricate(_f1);
        fabricator.fabricate(_f2);
        fabricator.fabricate(_f3);
        fabricator.fabricate(_f4);
        fabricator.fabricate(_f5);
    }
    /* Fabricate integer functions comparators */
    size_t modcpt = 0;
    for (auto papp : papps) {
        /* Modulos */
        if (papp.first.find("mod") == 0) {
            const std::string modrl = papp.first.substr(3);
            for (auto varapt : papp.second) {
                const std::string& vloc = varapt.at(0);
                const std::string locid = "mod" + std::to_string(modcpt++);
                smtparam_binding_set _binds;
                _binds[1] = modrl;
                FabricationRule _f(FilterMode::Conjunctive, FabricationPolicy::Apply_Simple,
                                   smt_mod_f, _binds, locid);
                const FabricationFilter _exact(FilterPolicy::Content_Include, vloc);
                _f.add_filter(_exact);
                fabricator.fabricate(_f);
                for (int divisor = 0; divisor < std::atoi(modrl.c_str()); ++divisor) {
                    smtparam_binding_set _binds;
                    _binds[1] = std::to_string(divisor);
                    const FabricationFilter _local(FilterPolicy::Annotation_Include, locid);
                    FabricationRule _g(FilterMode::Conjunctive, FabricationPolicy::Apply_Simple,
                                       smt_eq_f("Int"), _binds, locid);
                    _g.add_filter(_local);
                    fabricator.fabricate(_g);
                    FabricationRule _h(FilterMode::Conjunctive, FabricationPolicy::Apply_Simple,
                                       smt_not_f, locid + "n");
                    _h.add_filter(_local);
                    fabricator.fabricate(_h);
                }
            }
        }
    }
}

template<typename SourceT>
static const GenerationSet loc_generate(const SourceT& source) {
    GenerationSet result;
    SmtLitFabricator& fabricator = result.get_fabricator();
    why3cpp::ExtractorParser parser(source);
    for (const std::pair<std::string, std::string>& v : parser.getVars()) {
        fabricator.insert(smtlit_t(v.first, from_whyml_type(v.second)), annot_core_const);
    }
    for (const std::pair<std::string, std::string>& l : parser.getLits()) {
        fabricator.insert(smtlit_t(l.first, from_whyml_type(l.second)), annot_core_magic);
    }
    for (const std::string& ident : parser.getRefs()) {
        fabricator.annotate(ident, why3cpp::annot_whyml_ref);
    }
    loc_fabricate(fabricator, parser);
    FiltrationRule bool_filter(FilterMode::Conjunctive);
    bool_filter.add_filter(FabricationFilter(FilterPolicy::Type_Include, smt_bool));
    fabricator.filter(bool_filter, true);
    return result;
}

const smtlib2::GenerationSet why3cpp::generate_literals_whyml(const std::string& filename) {
    // Wrap through the smtlib2utils file interface
    return loc_generate<std::string>(filename);
}
