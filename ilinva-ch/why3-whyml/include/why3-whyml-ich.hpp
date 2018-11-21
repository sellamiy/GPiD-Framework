#ifndef WHY3_WHYML_ICH_FOR_GPID__HPP
#define WHY3_WHYML_ICH_FOR_GPID__HPP

#include "why3-whyml-source.hpp"

namespace gpid {

    class W3WML_ICH {
        W3WML_Template problem;
        W3WML_LSet plits;
        std::set<size_t>::iterator invariants_iter;

        std::list<W3WML_Constraint> literals;
    public:
        using ConstraintT = W3WML_Constraint;
        using ContextManagerT = std::set<std::string>; // Reference-typed variables
        using LoopIdentifierT = size_t;
        static const W3WML_Constraint C_False;

        W3WML_ICH(const std::string& filename)
            : problem(filename),
              plits(filename),
              invariants_iter(problem.getInvariantIds().begin())
        {}

        inline void strengthen(LoopIdentifierT id, ConstraintT cons) {
            problem.getInvariant(id).conj.push_back(cons);
        }

        inline void release(LoopIdentifierT id) {
            // Check required for first strengthening
            if (!problem.getInvariant(id).conj.empty()) {
                problem.getInvariant(id).conj.pop_back();
            }
        }

        bool isProven();

        const std::string generateAbductionProblem(LoopIdentifierT);

        const std::list<ConstraintT>& generateSourceLiterals(LoopIdentifierT);

        std::set<std::string>& generateContext(LoopIdentifierT);

        LoopIdentifierT selectUnprovenBlock();

        inline void exportSource(const std::string& filename) const {
            problem.save_to(filename);
        }
        inline void exportSource(std::ostream& out) const {
            out << problem;
        }

    };

}

#endif
