#define WHY3_WHYML_IPH_FOR_GPID__IPH_CONTROL__CPP

#include <fstream>
#include <abdulot/utils/abducibles-utils.hpp>
#include <why3-problem-control-wrapper.hpp>

#define WHYML_TEMPORARY_SOURCEFILE "temp_gpid_ilinva_w3wml.mlw"
#define SMTV2_TEMPORARY_ABDUCEFILE "temp_gpid_ilinva_abduce.smt2"

static const size_t ILLEGAL_BLOCK_DATA = (size_t)(-1);

using namespace abdulot;

const std::string Why3_ProblemController::w3opt_solver = "solver";
const std::string Why3_ProblemController::w3opt_vcinject = "vcinject";
const std::string Why3_ProblemController::w3opt_tlim = "tlim";

const std::string Why3_ProblemController::w3opt_fwdemptexpl = "fwdemptexpl";
const std::string Why3_ProblemController::w3opt_fwdinitexpl = "fwdinitexpl";
const std::string Why3_ProblemController::w3opt_cmapmode = "cmapmode";

const std::vector<std::string> Why3_ProblemController::w3opt_optlist = {
    Why3_ProblemController::w3opt_solver,
    Why3_ProblemController::w3opt_vcinject,
    Why3_ProblemController::w3opt_tlim,
    Why3_ProblemController::w3opt_fwdemptexpl,
    Why3_ProblemController::w3opt_fwdinitexpl,
    Why3_ProblemController::w3opt_cmapmode
};

static inline size_t tlim_contract(const std::string& tlim) {
    size_t loc = tlim.find('.');
    if (loc == std::string::npos) {
        return std::stoi(tlim);
    } else {
        return std::stoi(tlim.substr(0, loc));
    }
}

static inline why3cpp::VCInjectionMode deduce_inject_mode(const std::string& why3solv) {
    return why3solv == "Alt-Ergo" ?
        why3cpp::VCInjectionMode::AltErgo :
        why3cpp::VCInjectionMode::Classic;
}

why3cpp::ProofResult Why3_ProblemController::getWhy3Proof() {
    sourcedata.save_to(WHYML_TEMPORARY_SOURCEFILE, cmap);
    why3cpp::ProofResult
        proofResult = why3cpp::prove(WHYML_TEMPORARY_SOURCEFILE,
                                     getStringOption(w3opt_solver),
                                     getBoolOption(w3opt_vcinject),
                                     deduce_inject_mode(getStringOption(w3opt_solver)),
                                     tlim_contract(getStringOption(w3opt_tlim)));
    cachepr(proofResult);
    return proofResult;
}

static bool isStrengthenable
(const why3cpp::ProofResult& proofResult, const why3cpp::ProblemShape& pshape, bool forwardEmpty=false, bool forwardInit=false) {
    // TODO: Update this method to switch it with a better one
    for (auto res : proofResult.getResults())
        if (!why3cpp::proved(res.second))
            if (!isStrengthenableExplanation(pshape.at(res.first).expl, forwardEmpty, forwardInit))
                return false;
    return true;
}

ilinva::IphState Why3_ProblemController::proofCheck() {
    if (!prcached)
        getWhy3Proof();
    return ilinva::IphState(getCachedPr().isComplete(),
                            isStrengthenable(getCachedPr(), explshape, getBoolOption(w3opt_fwdemptexpl), getBoolOption(w3opt_fwdinitexpl)));
}

bool Why3_ProblemController::hasNextUnprovenBlock(size_t id) {
    blockcache.resize(id + 1);
    if (!prcached)
        getWhy3Proof();
    return blockgen.canGenerateBlock(getCachedPr(), blockcache.at(id));
}

size_t Why3_ProblemController::selectUnprovenBlock(size_t id) {
    blockcache.resize(id + 1);
    if (!prcached)
        getWhy3Proof();
    block_t bdata = blockgen.generateBlock(getCachedPr(), blockcache.at(id));
    if (bdata.first == ILLEGAL_BLOCK_DATA || bdata.second == ILLEGAL_BLOCK_DATA)
        snlog::l_internal() << "Generating incorrect proof block" << snlog::l_end;
    blockcache.at(id).insert(bdata);
    blockid_t bid = newblockid();
    blockmap[bid] = bdata;
    return bid;
}

const std::string Why3_ProblemController::generateAbductionProblem(blockid_t id) {
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
