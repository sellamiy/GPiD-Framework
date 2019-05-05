#define WHY3_WHYML_IPH_FOR_GPID__CONTEXT__CPP

#include <fstream>
#include <stdutils/random.hpp>
#include <smtlib2tools/fileutils.hpp>
#include <why3cpp/why3utils.hpp>
#include <abdulot/utils/abducibles-utils.hpp>
#include <ugly/SqueezePrefix.hpp>
#include <why3-context-wrapper.hpp>

using namespace abdulot;

const Why3_Constraint Why3_Prop_Ctx::getCandidateConstraint() {
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
    return Why3_Constraint(ss.str());
}

const std::vector<Why3_Constraint> Why3_Prop_Ctx::getCandidateConstraintDSplit() {
    std::vector<Why3_Constraint> res;
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
