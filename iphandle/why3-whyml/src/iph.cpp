#define WHY3_WHYML_IPH_FOR_GPID__IPH__CPP

#include <fstream>
#include <stdutils/random.hpp>
#include <smtlib2tools/smtlib2-fileutils.hpp>
#include <why3cpp/why3cpp.hpp>
#include <abdulot/utils/abducibles-utils.hpp>
#include <ugly/PineapplePrefix.hpp>
#include <why3-whyml-iph.hpp>

#define WARN_ONCE_D(lvar, wdata) if (!(lvar)) { snlog::l_warn() << "@" << __FILE__ << ":l" << __LINE__ << wdata << snlog::l_end; lvar = true; }

using namespace abdulot;

const W3WML_Constraint W3WML_IPH::C_False = W3WML_Constraint("false");

W3WML_Prop_Ctx W3WML_IPH::generateStrengheningContext
(PropIdentifierT id, const std::string& overrider, bool shuffle) {
    const std::string filename = problem.generateAbductionProblem(id);
    generateSourceLiterals(id, overrider, shuffle);
    return W3WML_Prop_Ctx
        (filename, literals,
         problem.getCandidateConjunction(id),
         cmap, translations, problem.getInternalPropertyIdentitifer(id),
         problem.getStringOption(W3WML_ProblemController::w3opt_solver),
         problem.getBoolOption(W3WML_ProblemController::w3opt_vcinject),
         problem.getStringOption(W3WML_ProblemController::w3opt_tlim),
         problem.getSourceCopy());
}

struct W_AbdStorerHandler : public GenericHandler {
    std::vector<std::string>& storage;
    std::set<std::string>& refs;
    const why3cpp::Why3ConvertMap& cmap;
    W_AbdStorerHandler(std::vector<std::string>& storage, std::set<std::string>& refs,
                       const why3cpp::Why3ConvertMap& cmap)
        : storage(storage), refs(refs), cmap(cmap) {}
    virtual void allocate(const std::string, size_t) override {}
    virtual void handleAbducible(const std::string& abd) override {
        storage.push_back(why3cpp::SmtBackwardConvert(abd, cmap));
    }
    virtual void handleReference(const std::string& ref) override {
        refs.insert(ref);
    }
};

void W3WML_IPH::loadOverridingAbducibles(const std::string& overrider, bool shuffle) {
    std::set<std::string> refs;
    W_AbdStorerHandler hdler(overrides[overrider], refs, cmap);
    loadAbduceData(overrider, hdler);
    cmap.addRefs(refs);
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

template<> const std::string W3WML_IPH::sanitizeLiteral<SymbolChecker>
(const std::string& lit, PropIdentifierT, const SymbolChecker& schecker) {
    if (schecker.visit(lisptp::parse(lit)))
        return lit;
    else
        return "";
}

static void generateTranslationMap
(const smtlib2::smtfile_decls& sdecls, std::map<std::string, std::string>& translations) {
    translations.clear();
    ugly::pineapple_squeeze_autostore(sdecls.get_set(), translations);
    // for (const auto& tm : translations)
    //     snlog::l_notif() << tm.first << " ---> " << tm.second << snlog::l_end;
}

void W3WML_IPH::generateSourceLiterals
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
                literals.push_back(W3WML_Constraint(slit));
        }
        cmap.addRefs(plits.getReferences());
    } else {
        // Read from overriding file
        if (overrides[overrider].empty())
            loadOverridingAbducibles(overrider, shuffle);
        for (const std::string& lit : overrides[overrider]) {
            const std::string slit = sanitizeLiteral(lit, id, schecker);
            if (slit.length() > 0)
                literals.push_back(W3WML_Constraint(slit));
        }
    }
    if (literals.empty()) {
        snlog::l_fatal() << "Abducible literal generation for block " << id
                         << " did not generate any literal!" << snlog::l_end;
    }
}

const W3WML_Constraint W3WML_Prop_Ctx::getCandidateConstraint() {
    std::stringstream ss;
    if (candidate.size() > 0) {
        if (candidate.size() > 1)
            ss << "(and ";
        for (auto& part : candidate)
            ss << part;
        if (candidate.size() > 1)
            ss << ")";
    } else {
        ss << "true";
    }
    return W3WML_Constraint(ss.str());
}

const std::vector<W3WML_Constraint> W3WML_Prop_Ctx::getCandidateConstraintDSplit() {
    std::vector<W3WML_Constraint> res;
    for (auto& part : candidate) {
        auto ftree = lisptp::parse(part);
        if (ftree->isCall() && (ftree->getValue() == "or" || ftree->getValue() == "OR"))
            for (auto leaf : ftree->getLeaves())
                res.push_back(leaf->str());
        else
            res.push_back(part);
    }
    return res;
}
