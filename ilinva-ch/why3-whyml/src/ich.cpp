#define WHY3_WHYML_ICH_FOR_GPID__ICH__CPP

#include <fstream>
#include <snlog/snlog.hpp>
#include <why3wrap/why3wrap.hpp>
#include <why3-whyml-ich.hpp>

#define WHYML_TEMPORARY_SOURCEFILE "temp_gpid_ilinva_w3wml.mlw"
#define SMTV2_TEMPORARY_ABDUCEFILE "temp_gpid_ilinva_abduce.smt2"

using namespace gpid;

const W3WML_Constraint W3WML_ICH::C_False = W3WML_Constraint("false");

bool W3WML_ICH::isProven() {
    problem.save_to(WHYML_TEMPORARY_SOURCEFILE);
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

std::set<std::string>& W3WML_ICH::generateContext(LoopIdentifierT) {
    return plits.getReferences();
}
