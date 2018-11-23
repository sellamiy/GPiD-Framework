#define WHY3_WHYML_ICH_FOR_GPID__ICH__CPP

#include <fstream>
#include <sstream>
#include <snlog/snlog.hpp>
#include <why3wrap/why3wrap.hpp>
#include <why3-whyml-ich.hpp>

#define WHYML_TEMPORARY_SOURCEFILE "temp_gpid_ilinva_w3wml.mlw"
#define SMTV2_TEMPORARY_ABDUCEFILE "temp_gpid_ilinva_abduce.smt2"

using namespace gpid;

const W3WML_Constraint W3WML_ICH::C_False = W3WML_Constraint("false");

bool W3WML_ICH::isProven() {
    problem.save_to(WHYML_TEMPORARY_SOURCEFILE, plits.getReferences());
    snlog::l_warn() << "@" << __FILE__ << ":l" << __LINE__
                    << " TODO: Select Why3 Prover via Options "<< snlog::l_end;
    return why3wrap::prove(WHYML_TEMPORARY_SOURCEFILE, "CVC4").isComplete();
}

const std::string W3WML_ICH::generateAbductionProblem(LoopIdentifierT) {
    snlog::l_warn() << "@" << __FILE__ << ":l" << __LINE__
                    << " TODO: Select Why3 Prover via Options "<< snlog::l_end;
    snlog::l_warn() << "@" << __FILE__ << ":l" << __LINE__
                    << " TODO: Abduction problem should depend on loop Id "<< snlog::l_end;
    std::ofstream ofs;
    ofs.open(SMTV2_TEMPORARY_ABDUCEFILE);
    ofs << why3wrap::prove(WHYML_TEMPORARY_SOURCEFILE, "CVC4").firstUnproven();
    ofs.close();
    return SMTV2_TEMPORARY_ABDUCEFILE;
}

W3WML_ICH::LoopIdentifierT W3WML_ICH::selectUnprovenBlock() {
    // TODO: Adapt on what follows v|
    snlog::l_warn() << "For Now, loop invariants cannot be distinguished from" << snlog::l_end;
    snlog::l_warn() << " their source file. This means that a loop-proof check" << snlog::l_end;
    snlog::l_warn() << " is equivalent to a file-proof check. This also means" << snlog::l_end;
    snlog::l_warn() << " that this version actually should not handle programs" << snlog::l_end;
    snlog::l_warn() << " containing more than one loop." << snlog::l_end;
    snlog::l_warn() << __FILE__ << " : " << __LINE__ << snlog::l_end;
    snlog::l_info() << "Using loop-id rotation as a temporary solution" << snlog::l_end;
    LoopIdentifierT res = *invariants_iter;
    invariants_iter++;
    if (invariants_iter == problem.getInvariantIds().end()) {
        invariants_iter = problem.getInvariantIds().begin();
    }
    return res;
}

const std::list<W3WML_Constraint>& W3WML_ICH::generateSourceLiterals(LoopIdentifierT) {
    if (literals.empty()) {
        for (const std::string& lit : plits.getLiterals()) {
            literals.push_back(W3WML_Constraint(lit));
        }
    }
    return literals;
}

W3WML_Loop_Ctx W3WML_ICH::generateContext(LoopIdentifierT lid) {
    return W3WML_Loop_Ctx(plits.getReferences(), problem.getInvariant(lid).conj);
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
    res.push_back(getCandidateConstraint());
    for (auto part : candidate) {
        auto ftree = lisptp::parse(part);
        if (ftree->isCall() && (ftree->getValue() == "or" || ftree->getValue() == "OR"))
            for (auto leaf : ftree->getLeaves())
                res.push_back(leaf->str());
    }
    return res;
}
