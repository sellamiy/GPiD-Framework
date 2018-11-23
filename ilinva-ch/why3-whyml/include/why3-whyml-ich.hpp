#ifndef WHY3_WHYML_ICH_FOR_GPID__HPP
#define WHY3_WHYML_ICH_FOR_GPID__HPP

#include "why3-whyml-source.hpp"

namespace gpid {

    class W3WML_Loop_Ctx {
        const std::set<std::string>& refs;
        std::list<const std::string>& candidate;
    public:
        W3WML_Loop_Ctx(const std::set<std::string>& refs, std::list<const std::string>& candidate)
            : refs(refs), candidate(candidate) {}
        W3WML_Loop_Ctx(const W3WML_Loop_Ctx& o)
            : refs(o.refs), candidate(o.candidate) {}
        inline const std::set<std::string>& getRefs() const { return refs; }
        inline std::list<const std::string>& getCandidate() { return candidate; }

        const W3WML_Constraint getCandidateConstraint();
        const std::list<W3WML_Constraint> getCandidateConstraintDSplit();
    };

    class W3WML_ICH {
        W3WML_Template problem;
        W3WML_LSet plits;
        std::set<size_t>::iterator invariants_iter;

        std::list<W3WML_Constraint> literals;
    public:
        using ConstraintT = W3WML_Constraint;
        using ContextManagerT = W3WML_Loop_Ctx;
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

        ContextManagerT generateContext(LoopIdentifierT);

        LoopIdentifierT selectUnprovenBlock();

        inline void exportSource(const std::string& filename) const {
            problem.save_to(filename, plits.getReferences());
        }
        inline void exportSource(std::ostream& out) const {
            write(out, problem, plits.getReferences());
        }

    };

}

#endif
