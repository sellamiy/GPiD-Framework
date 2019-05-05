#ifndef WHY3_WHYML_IPH_FOR_GPID__EXPLANATIONS_UTILS__HPP
#define WHY3_WHYML_IPH_FOR_GPID__EXPLANATIONS_UTILS__HPP

#include <string>
#include <snlog/snlog.hpp>

static inline bool isStrengthenableExplanation(const std::string& expl, bool forwardEmpty=false) {
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
        || (forwardEmpty && expl == "")
        ;
}

static inline bool isForwardingExplanation(const std::string& expl) {
    return expl == "expl:loop invariant preservation";
}

#endif
