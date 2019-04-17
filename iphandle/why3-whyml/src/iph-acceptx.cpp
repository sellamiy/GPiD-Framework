#define WHY3_WHYML_IPH_FOR_GPID__IPH_ACCEPT_CONTEXTUAL__CPP

#include <why3-whyml-iph.hpp>

using namespace abdulot;

#define ACCEPTX_CORE_NAME ".local.acceptx.mlw"

/* TODO: WARNING: This MUST be replaced by a concurrent version */
static size_t file_counter = 0;
static inline const std::string newFilename() {
    return std::to_string(file_counter++) + ACCEPTX_CORE_NAME;
}

/* TODO: This is a hardcoded copy of iph-control.cpp; Remove copy */
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

/* TODO: This is a hardcoded copy of iph-control.cpp; Remove copy */
static bool isStrengthenable(const why3cpp::ProofResult& proofResult) {
    // TODO: Update this method to switch it with a better one
    for (auto expl : proofResult.getExplanations())
        if (!why3cpp::proved(expl.second))
            if (!isStrengthenableExplanation(why3cpp::expl(expl.second)))
                return false;
    return true;
}

bool W3WML_IPH::acceptContextualConstraint(const W3WML_Constraint& cons, W3WML_Prop_Ctx& iphctx) {
    size_t property = iphctx.getPropertyIdentifier();
    const std::string filename = newFilename();
    iphctx.accessSourceCopy().getProperty(property).conj.push_back(cons.str());
    iphctx.accessSourceCopy().save_to(filename, iphctx.getCMap());
    why3cpp::ProofResult proofResult
        = why3cpp::prove(filename, iphctx.getWhy3Solver(), iphctx.performReorder());
    iphctx.accessSourceCopy().getProperty(property).conj.pop_back();
    return isStrengthenable(proofResult);
}
