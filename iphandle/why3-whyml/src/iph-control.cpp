#define WHY3_WHYML_IPH_FOR_GPID__IPH_CONTROL__CPP

#include <fstream>
#include <snlog/snlog.hpp>
#include <stdutils/collections.hpp>
#include <why3cpp/why3cpp.hpp>
#include <abdulot/utils/abducibles-utils.hpp>
#include <why3-whyml-controller.hpp>

#define WHYML_TEMPORARY_SOURCEFILE "temp_gpid_ilinva_w3wml.mlw"
#define SMTV2_TEMPORARY_ABDUCEFILE "temp_gpid_ilinva_abduce.smt2"

#define WARN_ONCE_D(lvar, wdata) if (!(lvar)) { snlog::l_warn() << "@" << __FILE__ << ":l" << __LINE__ << wdata << snlog::l_end; lvar = true; }

static const size_t ILLEGAL_BLOCK_DATA = (size_t)(-1);

using namespace abdulot;

const std::string W3WML_ProblemController::w3opt_solver = "solver";
const std::string W3WML_ProblemController::w3opt_vcreorder = "vcreorder";

void W3WML_ShapeDetector::detectVCShape(const why3cpp::ProofResult& pr) {
    for (auto& expl : pr.getExplanations())
        vc_shape[expl.first] = expl.second;
}

bool W3WML_ShapeDetector::canGenerateBlock
(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const {
    snlog::l_warn() << "NOT IMPLEM CAN GENERATE BLOCK SHAPE DETECTECOR" << snlog::l_end;
    return false;
}

block_t W3WML_ShapeDetector::generateBlock
(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const {
    snlog::l_warn() << "NOT IMPLEM GENERATE BLOCK SHAPE DETECTECOR" << snlog::l_end;
    return block_t(ILLEGAL_BLOCK_DATA, ILLEGAL_BLOCK_DATA);
}

why3cpp::ProofResult W3WML_ProblemController::getWhy3Proof() {
    sourcedata.save_to(WHYML_TEMPORARY_SOURCEFILE, cmap);
    why3cpp::ProofResult
        proofResult = why3cpp::prove(WHYML_TEMPORARY_SOURCEFILE,
                                     getStringOption(w3opt_solver),
                                     getBoolOption(w3opt_vcreorder));
    if (!shape.isVCShaped()) {
        shape.detectVCShape(proofResult);
    }
    cachepr(proofResult);
    return proofResult;
}

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
    // TODO: Update this method to switch it with a better one
    for (auto expl : proofResult.getExplanations())
        if (!isStrengthenableExplanation(expl.second))
            return false;
    return true;
}

ilinva::IphState W3WML_ProblemController::proofCheck() {
    if (!prcached)
        getWhy3Proof();
    return ilinva::IphState(getCachedPr().isComplete(), isStrengthenable(getCachedPr()));
}

bool W3WML_ProblemController::hasNextUnprovenBlock(size_t id) {
    blockcache.resize(id + 1);
    if (!prcached)
        getWhy3Proof();
    return shape.canGenerateBlock(getCachedPr(), blockcache.at(id + 1));
}

size_t W3WML_ProblemController::selectUnprovenBlock(size_t id) {
    blockcache.resize(id + 1);
    if (!prcached)
        getWhy3Proof();
    block_t bdata = shape.generateBlock(getCachedPr(), blockcache.at(id + 1));
    if (bdata.first == ILLEGAL_BLOCK_DATA || bdata.second == ILLEGAL_BLOCK_DATA)
        snlog::l_internal() << "Generating incorrect proof block" << snlog::l_end;
    blockcache.at(id).insert(bdata);
    blockid_t bid = newblockid();
    blockmap[bid] = bdata;
    return bid;
}

const std::string W3WML_ProblemController::generateAbductionProblem(blockid_t id) {
    auto vc = vc_ident(blockmap, id);
    if (!prcached)
        getWhy3Proof();
    std::ofstream ofs;
    ofs.open(SMTV2_TEMPORARY_ABDUCEFILE);
    ofs << getCachedPr().getSmtFile(vc);
    ofs.close();
    return SMTV2_TEMPORARY_ABDUCEFILE;
}

void W3WML_ProblemController::generateSourceLiterals
(blockid_t id, std::list<W3WML_Constraint>& literals, const std::string& overrider,
 std::map<std::string, std::list<std::string>>& overrides) {
    snlog::l_warn() << "NOT IMPLEM GENERATE SOURFC LITERALS POBLEMS CONTROLLER" << snlog::l_end;
}
