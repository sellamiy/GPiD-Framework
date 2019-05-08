#define WHY3_WHYML_IPH_FOR_GPID__IPH_ACCEPT_CONTEXTUAL__CPP

#include <why3-wrapped-iph.hpp>

using namespace abdulot;

#define ACCEPTX_CORE_NAME ".local.acceptx.mlw"

/* TODO: WARNING: This MUST be replaced by a concurrent version */
static size_t file_counter = 0;
static inline const std::string newFilename() {
    return std::to_string(file_counter++) + ACCEPTX_CORE_NAME;
}

/* TODO: This is a hardcoded copy of iph-control.cpp; Remove copy */
static bool isStrengthenable
(const why3cpp::ProofResult& proofResult, const why3cpp::ProblemShape& pshape, bool forwardEmpty=false, bool forwardInit=false) {
    // TODO: Update this method to switch it with a better one
    for (auto res : proofResult.getResults())
        if (!why3cpp::proved(res.second))
            if (!isStrengthenableExplanation(pshape.at(res.first).expl, forwardEmpty, forwardInit))
                return false;
    return true;
}

/* TODO: This is a hardcoded copy of iph-control.cpp; Remove copy */
static inline size_t tlim_contract(const std::string& tlim) {
    size_t loc = tlim.find('.');
    if (loc == std::string::npos) {
        return std::stoi(tlim);
    } else {
        return std::stoi(tlim.substr(0, loc));
    }
}

/* TODO: This is a hardcoded copy of iph-control.cpp; Remove copy */
static inline why3cpp::VCInjectionMode deduce_inject_mode(const std::string& why3solv) {
    return why3solv == "Alt-Ergo" ?
        why3cpp::VCInjectionMode::AltErgo :
        why3cpp::VCInjectionMode::Classic;
}

bool Why3_IPH::acceptContextualConstraint(const Why3_Constraint& cons, Why3_Prop_Ctx& iphctx) {
    size_t property = iphctx.getPropertyIdentifier();
    const std::string filename = newFilename();
    iphctx.accessSourceCopy().getProperty(property).conj.push_back(cons.str());
    iphctx.accessSourceCopy().save_to(filename, iphctx.getCMap());
    why3cpp::ProofResult proofResult
        = why3cpp::prove(filename, iphctx.getWhy3Solver(),
                         iphctx.performInjections(), deduce_inject_mode(iphctx.getWhy3Solver()),
                         tlim_contract(iphctx.getTlim()));
    iphctx.accessSourceCopy().getProperty(property).conj.pop_back();
    return isStrengthenable(proofResult, iphctx.getProblemShape(), iphctx.getForwardEmptyExplOpt(), iphctx.getForwardInitExplOpt());
}
