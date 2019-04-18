#ifndef WHY3_WHYML_IPH_FOR_GPID__HPP
#define WHY3_WHYML_IPH_FOR_GPID__HPP

#include <abdulot/ilinva/options.hpp>
#include "why3-whyml-controller.hpp"

#define WHY3_SOLVER_OPTION_DEFAULT "CVC4"

#define WHY3_CMAP_MODE_DEFAULT "auto"

class W3WML_Prop_Ctx {
    const std::string pfile;
    const std::vector<W3WML_Constraint>& literals;
    const std::vector<std::string>& candidate;
    const why3cpp::Why3ConvertMap& cmap;
    const std::map<std::string, std::string>& translations;

    const size_t propid;
    const std::string solverid;
    const std::string tlim;
    const bool preorder;

    std::shared_ptr<W3WML_Template> sourceCopy;
public:
    W3WML_Prop_Ctx(const std::string& pfile, const std::vector<W3WML_Constraint>& literals,
                   const std::vector<std::string>& candidate, const why3cpp::Why3ConvertMap& cmap,
                   const std::map<std::string, std::string>& translations, size_t propid,
                   const std::string& solverid, bool preorder, const std::string& tlim,
                   const std::shared_ptr<W3WML_Template>& source)
        : pfile(pfile), literals(literals), candidate(candidate),
          cmap(cmap), translations(translations), propid(propid),
          solverid(solverid), tlim(tlim), preorder(preorder), sourceCopy(source) {}
    W3WML_Prop_Ctx(const W3WML_Prop_Ctx& o)
        : pfile(o.pfile), literals(o.literals), candidate(o.candidate),
          cmap(o.cmap), translations(o.translations), propid(o.propid),
          solverid(o.solverid), tlim(o.tlim), preorder(o.preorder), sourceCopy(o.sourceCopy) {}

    inline const std::string& getProblemFile() const { return pfile; }
    inline const std::vector<W3WML_Constraint>& getLiterals() const { return literals; }
    inline const why3cpp::Why3ConvertMap& getCMap() const { return cmap; }
    inline const std::vector<std::string>& getCandidate() const { return candidate; }
    inline const std::map<std::string, std::string>& getTranslationMap() const { return translations; }
    inline constexpr size_t getPropertyIdentifier() const { return propid; }
    inline const std::string& getWhy3Solver() const { return solverid; }
    inline const std::string& getTlim() const { return tlim; }
    inline constexpr bool performReorder() const { return preorder; }

    inline W3WML_Template& accessSourceCopy() { return *sourceCopy; }

    const W3WML_Constraint getCandidateConstraint();
    const std::vector<W3WML_Constraint> getCandidateConstraintDSplit();
};

struct W3WML_Opthelpers {
    static inline bool is_str_true(const std::string& s) {
        return s == "true" || s == "TRUE" || s == "True";
    }

    static inline bool is_str_false(const std::string& s) {
        return s == "false" || s == "FALSE" || s == "False";
    }
};

class W3WML_IPH {
public:
    using ConstraintT = W3WML_Constraint;
    using ContextManagerT = W3WML_Prop_Ctx;
    using PropIdentifierT = W3WML_ProblemController::blockid_t;
private:
    std::map<size_t, std::set<size_t>::iterator> invariants_iter;

    std::vector<W3WML_Constraint> literals;
    why3cpp::Why3ConvertMap cmap;
    std::map<std::string, std::string> translations;

    std::map<std::string, std::vector<std::string>> overrides;

    stringoptionmap_t local_opts;
    booloptionmap_t local_bopts;

    W3WML_ProblemController problem;
    W3WML_LSet plits;

    template<typename InternalT>
    const std::string sanitizeLiteral
    (const std::string& lit, PropIdentifierT id, const InternalT& o);
public:
    static const W3WML_Constraint C_False;

    static void configure(abdulot::ilinva::IlinvaOptions& opts);

    static bool acceptContextualConstraint(const W3WML_Constraint& constraint, W3WML_Prop_Ctx& iphctx);

    W3WML_IPH(const std::string& filename, bool overriden, bool shuffle,
              const std::map<std::string, std::string>& hopts)
        : cmap(stdutils::inmap(hopts, W3WML_ProblemController::w3opt_cmapmode) ?
               hopts.at(W3WML_ProblemController::w3opt_cmapmode) : WHY3_CMAP_MODE_DEFAULT),
          problem(filename, cmap, local_opts, local_bopts),
          plits(filename, cmap, overriden, shuffle)
    {
        // Set default Why3 solver to CVC4
        setOption(W3WML_ProblemController::w3opt_solver, WHY3_SOLVER_OPTION_DEFAULT);
        setOption(W3WML_ProblemController::w3opt_vcreorder, false);
        setOption(W3WML_ProblemController::w3opt_tlim, WHY3_DEFAULT_SOLVER_TLIM);

        for (const std::pair<std::string, std::string>& hopt : hopts) {
            if (W3WML_Opthelpers::is_str_true(hopt.second))
                setOption(hopt.first, true);
            else if (W3WML_Opthelpers::is_str_false(hopt.second))
                setOption(hopt.first, false);
            else
                setOption(hopt.first, hopt.second);
        }
    }

    inline void setOption(const std::string& optname, const std::string& optvalue) {
        local_opts[optname] = optvalue;
    }

    inline void setOption(const std::string& optname, bool optvalue) {
        local_bopts[optname] = optvalue;
    }

    inline void strengthen(PropIdentifierT id, ConstraintT cons) {
        cmap.setLocalId(id);
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

    void generateSourceLiterals(PropIdentifierT id, const std::string& overrider, bool shuffle);

    ContextManagerT generateStrengheningContext
    (PropIdentifierT id, const std::string& overrider, bool shuffle);

    inline void exportSource(const std::string& filename) const {
        problem.exportSource(filename);
    }

    inline void exportSource(std::ostream& out) const {
        problem.exportSource(out);
    }

    void loadOverridingAbducibles(const std::string& overrider, bool shuffle);

};

#endif
