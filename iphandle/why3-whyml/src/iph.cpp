#define WHY3_WHYML_IPH_FOR_GPID__IPH__CPP

#include <fstream>
#include <snlog/snlog.hpp>
#include <stdutils/collections.hpp>
#include <why3cpp/why3cpp.hpp>
#include <abdulot/utils/abducibles-utils.hpp>
#include <why3-whyml-iph.hpp>

using namespace abdulot;

const W3WML_Constraint W3WML_IPH::C_False = W3WML_Constraint("false");

/*
const std::list<W3WML_Constraint>& W3WML_IPH::generateSourceLiterals
(PropIdentifierT, const std::string& overrider) {
    if (literals.empty()) {
        if (overrider.empty()) {
            for (const std::string& lit : plits.getLiterals()) {
                literals.push_back(W3WML_Constraint(lit));
            }
            refs = plits.getReferences();
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
*/

W3WML_Prop_Ctx W3WML_IPH::generateStrengheningContext(PropIdentifierT id, const std::string& overrider) {
    const std::string filename = problem.generateAbductionProblem(id);
    problem.generateSourceLiterals(id, literals, overrider, overrides);
    return W3WML_Prop_Ctx(filename, literals, problem.getCandidateConjunction(id), problem.getCMap());
}

struct W_AbdStorerHandler : public GenericHandler {
    std::list<std::string>& storage;
    std::set<std::string>& refs;
    W_AbdStorerHandler(std::list<std::string>& storage, std::set<std::string>& refs)
        : storage(storage), refs(refs) {}
    virtual void allocate(const std::string, size_t) override {}
    virtual void handleAbducible(const std::string& abd) override {
        storage.push_back(abd);
    }
    virtual void handleReference(const std::string& ref) override {
        refs.insert(ref);
    }
};

void W3WML_IPH::loadOverridingAbducibles(const std::string& overrider) {
    W_AbdStorerHandler hdler(overrides[overrider], refs);
    loadAbduceData(overrider, hdler);
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

const std::list<W3WML_Constraint> W3WML_Prop_Ctx::getCandidateConstraintDSplit() {
    std::list<W3WML_Constraint> res;
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
