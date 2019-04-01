#ifndef WHY3_WHYML_IPH_FOR_GPID__HPP
#define WHY3_WHYML_IPH_FOR_GPID__HPP

#include "why3-whyml-controller.hpp"

#define WHY3_SOLVER_OPTION_DEFAULT "CVC4"

class W3WML_Prop_Ctx {
    const std::string pfile;
    const std::list<W3WML_Constraint>& literals;
    std::list<const std::string>& candidate;
    const why3cpp::Why3ConvertMap& cmap;
public:
    W3WML_Prop_Ctx(const std::string& pfile, const std::list<W3WML_Constraint>& literals,
                   std::list<const std::string>& candidate, const why3cpp::Why3ConvertMap& cmap)
        : pfile(pfile), literals(literals), candidate(candidate), cmap(cmap) {}
    W3WML_Prop_Ctx(const W3WML_Prop_Ctx& o)
        : pfile(o.pfile), literals(o.literals), candidate(o.candidate), cmap(o.cmap) {}

    inline const std::string& getProblemFile() const { return pfile; }
    inline const std::list<W3WML_Constraint>& getLiterals() const { return literals; }
    inline const why3cpp::Why3ConvertMap& getCMap() const { return cmap; }
    inline std::list<const std::string>& getCandidate() { return candidate; }

    const W3WML_Constraint getCandidateConstraint();
    const std::list<W3WML_Constraint> getCandidateConstraintDSplit();
};

class W3WML_IPH {
public:
    using ConstraintT = W3WML_Constraint;
    using ContextManagerT = W3WML_Prop_Ctx;
    using PropIdentifierT = W3WML_ProblemController::blockid_t;
private:
    W3WML_ProblemController problem;
    W3WML_LSet plits;
    std::map<size_t, std::set<size_t>::iterator> invariants_iter;

    std::list<W3WML_Constraint> literals;
    why3cpp::Why3ConvertMap cmap;

    std::map<std::string, std::list<std::string>> overrides;

    stringoptionmap_t local_opts;
    booloptionmap_t local_bopts;

    const std::string sanitizeLiteral(PropIdentifierT id, const std::string& lit);
public:
    static const W3WML_Constraint C_False;

    W3WML_IPH(const std::string& filename, bool overriden)
        : problem(filename, cmap, local_opts, local_bopts),
          plits(filename, overriden)
    {
        // Set default Why3 solver to CVC4
        setOption(W3WML_ProblemController::w3opt_solver, WHY3_SOLVER_OPTION_DEFAULT);
        setOption(W3WML_ProblemController::w3opt_vcreorder, true);
    }

    inline void setOption(const std::string& optname, const std::string& optvalue) {
        local_opts[optname] = optvalue;
    }

    inline void setOption(const std::string& optname, bool optvalue) {
        local_bopts[optname] = optvalue;
    }

    inline void strengthen(PropIdentifierT id, ConstraintT cons) {
        problem.strengthen(id, cons);
    }

    inline void release(PropIdentifierT id) {
        problem.release(id);
    }

    inline abdulot::ilinva::IphState proofCheck() {
        return problem.proofCheck();
    }

    inline bool hasNextUnprovenBlock(size_t id) {
        return problem.hasNextUnprovenBlock(id);
    }

    inline PropIdentifierT selectUnprovenBlock(size_t id) {
        return problem.selectUnprovenBlock(id);
    }

    void generateSourceLiterals(PropIdentifierT id, const std::string& overrider);

    ContextManagerT generateStrengheningContext(PropIdentifierT id, const std::string& overrider);

    inline void exportSource(const std::string& filename) const {
        problem.exportSource(filename);
    }

    inline void exportSource(std::ostream& out) const {
        problem.exportSource(out);
    }

    void loadOverridingAbducibles(const std::string& overrider);

};

#endif
