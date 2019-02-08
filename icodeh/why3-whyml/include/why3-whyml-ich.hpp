#ifndef WHY3_WHYML_ICH_FOR_GPID__HPP
#define WHY3_WHYML_ICH_FOR_GPID__HPP

#include <abdulot/ilinva/ich-core.hpp>
#include "why3-whyml-source.hpp"

#define WHY3_SOLVER_OPTION_DEFAULT "CVC4"

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
    std::map<size_t, std::set<size_t>::iterator> invariants_iter;

    std::list<W3WML_Constraint> literals;

    std::map<std::string, std::list<std::string>> overrides;
    std::set<std::string> refs;

    std::map<std::string, std::string> local_opts;
public:
    using ConstraintT = W3WML_Constraint;
    using ContextManagerT = W3WML_Loop_Ctx;
    using LoopIdentifierT = size_t;
    static const W3WML_Constraint C_False;

    const std::string w3opt_solver = "solver";

    W3WML_ICH(const std::string& filename, bool overriden)
        : problem(filename),
          plits(filename, overriden)
    {
        setOption(w3opt_solver, WHY3_SOLVER_OPTION_DEFAULT); // Set default Why3 solver to CVC4
    }

    inline void setOption(const std::string& optname, const std::string& optvalue) {
        local_opts[optname] = optvalue;
    }

    inline const std::string& getOption(const std::string& optname) const {
        return local_opts.at(optname);
    }

    inline void strengthen(LoopIdentifierT id, ConstraintT cons) {
        problem.getInvariant(id).conj.push_back(cons);
        write(snlog::l_message() << "@C[" << id << "]: ",
              problem.getInvariant(id), refs) << snlog::l_end;
    }

    inline void release(LoopIdentifierT id) {
        // Check required for first strengthening
        if (!problem.getInvariant(id).conj.empty()) {
            problem.getInvariant(id).conj.pop_back();
        }
    }

    abdulot::ilinva::IchState proofCheck();

    const std::string generateAbductionProblem(LoopIdentifierT);

    const std::list<ConstraintT>& generateSourceLiterals(LoopIdentifierT, const std::string&);

    ContextManagerT generateContext(LoopIdentifierT);

    LoopIdentifierT selectUnprovenBlock(size_t id);

    void loadOverridingAbducibles(const std::string& overrider);

    inline void exportSource(const std::string& filename) const {
        problem.save_to(filename, refs);
    }
    inline void exportSource(std::ostream& out) const {
        write(out, problem, refs);
    }

};

#endif
