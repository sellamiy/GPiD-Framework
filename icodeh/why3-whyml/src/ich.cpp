#define WHY3_WHYML_ICH_FOR_GPID__ICH__CPP

#include <fstream>
#include <sstream>
#include <snlog/snlog.hpp>
#include <stdutils/collections.hpp>
#include <lisptp/lisptp.hpp>
#include <why3cpp/why3cpp.hpp>
#include <abdulot/utils/abducibles-utils.hpp>
#include <why3-whyml-ich.hpp>

#define WHYML_TEMPORARY_SOURCEFILE "temp_gpid_ilinva_w3wml.mlw"
#define SMTV2_TEMPORARY_ABDUCEFILE "temp_gpid_ilinva_abduce.smt2"

using namespace abdulot;

const W3WML_Constraint W3WML_ICH::C_False = W3WML_Constraint("false");

static inline bool isStrengthenableExplanation(const std::string& expl) {
    return expl == "expl:postcondition"
        || expl == "expl:exceptional postcondition"
        || expl == "expl:assertion"
        || expl == "expl:check"
        || expl == "expl:lemma"
        || expl == "expl:unreachable point" // TODO: Check relevancy
        || expl == "expl:loop bounds" // TODO: Check relevancy
        || expl == "expl:out of loop bounds" // TODO: Check relevancy
        || expl == "expl:loop invariant preservation"
        || expl == "expl:loop variant decrease" // TODO: Check relevancy
        || expl == "expl:variant decrease" // TODO: Check relevancy
        || expl == "expl:type invariant" // TODO: Check relevancy
        || expl == "expl:termination" // TODO: Check relevancy
        ;
}

static bool isStrengthenable(const why3cpp::ProofResult& proofResult) {
    for (auto expl : proofResult.getExplanations())
        if (!isStrengthenableExplanation(expl.second)) {
            snlog::l_error() << "Unstrengthenable explanation found: " << expl.second << snlog::l_end;
            return false;
        }
    return true;
}

ilinva::IchState W3WML_ICH::proofCheck() {
    problem.save_to(WHYML_TEMPORARY_SOURCEFILE, plits.getReferences());
    snlog::l_warn() << "@" << __FILE__ << ":l" << __LINE__
                    << " TODO: Select Why3 Prover via Options "<< snlog::l_end;
    why3cpp::ProofResult proofResult = why3cpp::prove(WHYML_TEMPORARY_SOURCEFILE, "CVC4");
    return ilinva::IchState(proofResult.isComplete(), isStrengthenable(proofResult));
}

const std::string W3WML_ICH::generateAbductionProblem(LoopIdentifierT) {
    snlog::l_warn() << "@" << __FILE__ << ":l" << __LINE__
                    << " TODO: Select Why3 Prover via Options "<< snlog::l_end;
    snlog::l_warn() << "@" << __FILE__ << ":l" << __LINE__
                    << " TODO: Abduction problem should depend on loop Id "<< snlog::l_end;
    std::ofstream ofs;
    ofs.open(SMTV2_TEMPORARY_ABDUCEFILE);
    ofs << why3cpp::prove(WHYML_TEMPORARY_SOURCEFILE, "CVC4").firstUnproven();
    ofs.close();
    return SMTV2_TEMPORARY_ABDUCEFILE;
}

W3WML_ICH::LoopIdentifierT W3WML_ICH::selectUnprovenBlock(size_t id) {
    // TODO: Adapt on what follows v|
    snlog::l_warn() << __FILE__ << " : " << __LINE__ << snlog::l_end
                    << snlog::l_warn << "**Fnlicd undistinction invariant-proof/file-proof"
                    << snlog::l_end << snlog::l_info
                    << "Using loop-id rotation as a temporary solution" << snlog::l_end;
    LoopIdentifierT res;
    if (stdutils::inmap(invariants_iter, id)) {
        res = *invariants_iter.at(id);
        invariants_iter.at(id)++;
        if (invariants_iter.at(id) == problem.getInvariantIds().end()) {
            invariants_iter[id] = problem.getInvariantIds().begin();
        }
    } else {
        invariants_iter[id] = problem.getInvariantIds().begin();
        res = *invariants_iter.at(id);
        invariants_iter.at(id)++;
    }
    return res;
}

const std::list<W3WML_Constraint>& W3WML_ICH::generateSourceLiterals
(LoopIdentifierT, const std::string& overrider) {
    if (literals.empty()) {
        if (overrider.empty()) {
            for (const std::string& lit : plits.getLiterals()) {
                literals.push_back(W3WML_Constraint(lit));
            }
        } else {
            // Read from overriding file
            if (overrides[overrider].empty())
                loadOverridingAbducibles(overrider);
            for (const std::string& lit : overrides[overrider]) {
                literals.push_back(W3WML_Constraint(lit));
            }
        }
    }
    return literals;
}

W3WML_Loop_Ctx W3WML_ICH::generateContext(LoopIdentifierT lid) {
    return W3WML_Loop_Ctx(plits.getReferences(), problem.getInvariant(lid).conj);
}

struct W_AbdStorerHandler : public AbducibleHandler {
    std::list<std::string>& storage;
    W_AbdStorerHandler(std::list<std::string>& storage) : storage(storage) {}
    virtual void allocate(const std::string, size_t) override {}
    virtual void handleAbducible(const std::shared_ptr<std::string>& abd) override {
        storage.push_back(*abd);
    }
};

void W3WML_ICH::loadOverridingAbducibles(const std::string& overrider) {
    W_AbdStorerHandler hdler(overrides[overrider]);
    loadAbducibles(overrider, hdler);
}

const W3WML_Constraint W3WML_Loop_Ctx::getCandidateConstraint() {
    std::stringstream ss;
    if (candidate.size() > 0) {
        if (candidate.size() > 1)
            ss << "(and ";
        for (auto part : candidate)
            ss << part;
        if (candidate.size() > 1)
            ss << ")";
    } else {
        ss << "true";
    }
    return W3WML_Constraint(ss.str());
}

const std::list<W3WML_Constraint> W3WML_Loop_Ctx::getCandidateConstraintDSplit() {
    std::list<W3WML_Constraint> res;
    for (auto part : candidate) {
        auto ftree = lisptp::parse(part);
        if (ftree->isCall() && (ftree->getValue() == "or" || ftree->getValue() == "OR"))
            for (auto leaf : ftree->getLeaves())
                res.push_back(leaf->str());
        else
            res.push_back(part);
    }
    return res;
}
