#define WHY3_WHYML_IPH_FOR_GPID__IPH__CPP

#include <fstream>
#include <stdutils/random.hpp>
#include <smtlib2tools/fileutils.hpp>
#include <abdulot/utils/abducibles-utils.hpp>
#include <ugly/SqueezePrefix.hpp>
#include <why3-wrapped-iph.hpp>

using namespace abdulot;

const Why3_Constraint Why3_IPH::C_False = Why3_Constraint("false");

Why3_Prop_Ctx Why3_IPH::generateStrengheningContext
(PropIdentifierT id, const std::string& overrider, bool shuffle) {
    const std::string filename = problem.generateAbductionProblem(id);
    generateSourceLiterals(id, overrider, shuffle);
    return Why3_Prop_Ctx
        (filename, problem.getProblemShape(), literals,
         problem.getCandidateConjunction(id),
         cmap, translations, problem.requiresForwarding(id),
         problem.getInternalPropertyIdentitifer(id),
         problem.getStringOption(Why3_ProblemController::w3opt_solver),
         problem.getBoolOption(Why3_ProblemController::w3opt_vcinject),
         problem.getBoolOption(Why3_ProblemController::w3opt_fwdemptexpl),
         problem.getBoolOption(Why3_ProblemController::w3opt_fwdinitexpl),
         problem.getStringOption(Why3_ProblemController::w3opt_tlim),
         problem.getStringOption(Why3_ProblemController::w3opt_configfile),
         problem.getSourceCopy());
}

struct W_AbdStorerHandler : public GenericHandler {
    std::vector<std::string>& storage;
    std::set<std::string>& refs;
    std::map<std::string, std::set<std::string>>& annots;
    const why3cpp::Why3ConvertMap& cmap;
    W_AbdStorerHandler(std::vector<std::string>& storage, std::set<std::string>& refs,
                       std::map<std::string, std::set<std::string>>& annots,
                       const why3cpp::Why3ConvertMap& cmap)
        : storage(storage), refs(refs), annots(annots), cmap(cmap) {}
    virtual void allocate(const std::string, size_t) override {}
    virtual void handleAbducible(const std::string& abd) override {
        storage.push_back(why3cpp::SmtBackwardConvert(abd, cmap));
    }
    virtual void handleReference(const std::string& ref) override {
        refs.insert(ref);
    }
    virtual void handleAnnotation(const std::string& ref, const std::string& annot) override {
        annots[annot].insert(ref);
    }
};

void Why3_IPH::loadOverridingAbducibles(const std::string& overrider, bool shuffle) {
    std::set<std::string> refs;
    std::map<std::string, std::set<std::string>> annots;
    W_AbdStorerHandler hdler(overrides[overrider], refs, annots, cmap);
    loadAbduceData(overrider, hdler);
    cmap.addRefs(refs);
    cmap.addAnnots(annots);
    if (shuffle)
        stdutils::shuffle(hdler.storage);
}

struct LitSanatizer_X101 : public lisptp::LispTreeVisitor<bool> {
    const smtlib2::smtfile_decls& symbols;
    LitSanatizer_X101(const smtlib2::smtfile_decls& symbols) : symbols(symbols) {}
protected:
    virtual bool handle_term(const std::string& t) const {
        return symbols.is_declared(t) || smtlib2::is_literal(t);
    }
    virtual bool handle_call(const std::string&, const std::vector<bool>& lvs) const {
        // TODO: check lvs accesses in range for readability of errors
        // TODO: Add usual logics declarations (from the selogic I suppose)
        // TODO: Better decl tests (quatified vars, etc.)
        // TODO: Handle function names declarations actually
        for (bool b : lvs) if (!b) return false;
        return true;
    }
};

/* Checker for which the visit function returns true iff
   all the elements of the visited tree are declared symbols */
using SymbolChecker = LitSanatizer_X101;

template<> const std::string Why3_IPH::sanitizeLiteral<SymbolChecker>
(const std::string& lit, PropIdentifierT, const SymbolChecker& schecker) {
    if (schecker.visit(lisptp::parse(lit)))
        return lit;
    else
        return "";
}

static void generateTranslationMap
(const smtlib2::smtfile_decls& sdecls, std::map<std::string, std::string>& translations) {
    translations.clear();
    ugly::squeeze_autostore(sdecls.get_set(), translations);
    // for (const auto& tm : translations)
    //     snlog::l_notif() << tm.first << " ---> " << tm.second << snlog::l_end;
}

void Why3_IPH::generateSourceLiterals
(PropIdentifierT id, const std::string& overrider, bool shuffle) {
    const std::string& pfile = problem.getBlockFile(id);
    smtlib2::smtfile_decls sdecls = smtlib2::extract_declarations(pfile);
    generateTranslationMap(sdecls, translations);
    SymbolChecker schecker(sdecls);
    if (!literals.empty()) {
        literals.clear();
    }
    if (overrider.empty()) {
        for (const std::string& lit : plits.getLiterals()) {
            const std::string slit = sanitizeLiteral(lit, id, schecker);
            if (slit.length() > 0)
                literals.push_back(Why3_Constraint(slit));
        }
        cmap.addRefs(plits.getReferences());
    } else {
        // Read from overriding file
        if (overrides[overrider].empty())
            loadOverridingAbducibles(overrider, shuffle);
        for (const std::string& lit : overrides[overrider]) {
            const std::string slit = sanitizeLiteral(lit, id, schecker);
            if (slit.length() > 0)
                literals.push_back(Why3_Constraint(slit));
        }
    }
    if (literals.empty()) {
        snlog::l_warn() << "Abducible literal generation for block " << id
                        << " did not generate any literal!" << snlog::l_end;
    }
}
