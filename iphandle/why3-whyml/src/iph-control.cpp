#define WHY3_WHYML_IPH_FOR_GPID__IPH_CONTROL__CPP

#include <fstream>
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

const std::string W3WML_ProblemController::w3opt_cmapmode = "cmapmode";

static inline bool is_property_bypasser_expl(const std::string& expl) {
    return expl == "expl:loop invariant init";
}

void W3WML_ShapeDetector::detectVCShape(const why3cpp::ProofResult& pr) {
    std::map<size_t, std::string>::iterator it = properties_shape.begin();
    bool before_start = true;
    for (auto& expl : pr.getExplanations()) {
        if (is_property_bypasser_expl(why3cpp::expl(expl.second))) {
            if (before_start) {
                before_start = false;
            } else {
                ++it;
                if (it == properties_shape.end()) {
                    snlog::l_warn() << "WhyML shape detector detected more loops"
                                    << " than invariants you have declared"
                                    << snlog::l_end;
                }
            }
        }
        vc_shape[expl.first] = why3cpp::expl(expl.second);
        maxp_shape[expl.first] = it->first;
    }
}

bool W3WML_ShapeDetector::canGenerateBlock
(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const {
    const block_t _dum = generateBlock(pr, cached);
    return _dum.first != ILLEGAL_BLOCK_DATA && _dum.second != ILLEGAL_BLOCK_DATA;
}

block_t W3WML_ShapeDetector::generateBlock
(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const {
    // TODO: Perform a better candidacy pruning with a better shape detection
    for (const auto& vcd : vc_shape) {
        if (pr.isProved(vcd.first))
            continue;
        for (const auto& propd : properties_shape) {
            if (propd.first > maxp_shape.at(vcd.first))
                /* Warning: This is based on the assumption that properties
                   identifers follow the same ordering as properties within
                   the source. This should be true.
                   If it is true, then this test gives the result we expect
                   because map iteration done by the detectVCShape is on an
                   std::map with sorted key indices */
                break;
            block_t _dum = block_t(vcd.first, propd.first);
            if (stdutils::ninset(cached, _dum))
                return _dum;
        }
    }
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
        if (!why3cpp::proved(expl.second))
            if (!isStrengthenableExplanation(why3cpp::expl(expl.second)))
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
    return shape.canGenerateBlock(getCachedPr(), blockcache.at(id));
}

size_t W3WML_ProblemController::selectUnprovenBlock(size_t id) {
    blockcache.resize(id + 1);
    if (!prcached)
        getWhy3Proof();
    block_t bdata = shape.generateBlock(getCachedPr(), blockcache.at(id));
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
    encacheBlockFile(id, SMTV2_TEMPORARY_ABDUCEFILE);
    return SMTV2_TEMPORARY_ABDUCEFILE;
}
