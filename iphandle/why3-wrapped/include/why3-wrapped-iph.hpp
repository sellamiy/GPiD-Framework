#ifndef WHY3_WHYML_IPH_FOR_GPID__HPP
#define WHY3_WHYML_IPH_FOR_GPID__HPP

#include <abdulot/ilinva/options.hpp>
#include "why3-problem-control-wrapper.hpp"
#include "why3-context-wrapper.hpp"
#include "why3-lset-wrapper.hpp"

#define WHY3_SOLVER_OPTION_DEFAULT "CVC4"

#define WHY3_CMAP_MODE_DEFAULT "auto"
#define WHY3_DEFAULT_EMPTY_EXPL_FWD_MODE false

struct Why3_Opthelpers {
    static inline bool is_str_true(const std::string& s) {
        return s == "true" || s == "TRUE" || s == "True";
    }

    static inline bool is_str_false(const std::string& s) {
        return s == "false" || s == "FALSE" || s == "False";
    }
};

class Why3_IPH {
public:
    using ConstraintT = Why3_Constraint;
    using ContextManagerT = Why3_Prop_Ctx;
    using PropIdentifierT = Why3_ProblemController::blockid_t;
private:
    std::map<size_t, std::set<size_t>::iterator> invariants_iter;

    std::vector<Why3_Constraint> literals;
    why3cpp::Why3ConvertMap cmap;
    std::map<std::string, std::string> translations;

    std::map<std::string, std::vector<std::string>> overrides;

    stringoptionmap_t local_opts;
    booloptionmap_t local_bopts;

    Why3_ProblemController problem;
    Why3_LSet plits;

    template<typename InternalT>
    const std::string sanitizeLiteral
    (const std::string& lit, PropIdentifierT id, const InternalT& o);
public:
    static const Why3_Constraint C_False;

    static void configure(abdulot::ilinva::IlinvaOptions& opts);

    static bool acceptContextualConstraint(const Why3_Constraint& constraint, Why3_Prop_Ctx& iphctx);

    static const std::vector<std::string>& getOptionsList() {
        return Why3_ProblemController::w3opt_optlist;
    }

    static void printInfos() {
        snlog::l_message() << "Why3 (via WhyML) Interface code handler" << snlog::l_end;
        auto& logger = snlog::l_message() << "Interface options:";
        for (const auto& optname : getOptionsList())
            logger << "\n    * " << optname;
        logger << snlog::l_end;
    }

    Why3_IPH(const std::string& filename, bool overriden, bool shuffle,
              const std::map<std::string, std::string>& hopts)
        : cmap(stdutils::inmap(hopts, Why3_ProblemController::w3opt_cmapmode) ?
               hopts.at(Why3_ProblemController::w3opt_cmapmode) : WHY3_CMAP_MODE_DEFAULT),
          problem(filename, cmap, local_opts, local_bopts),
          plits(filename, cmap, overriden, shuffle)
    {
        // Set default Why3 solver to CVC4
        setOption(Why3_ProblemController::w3opt_solver, WHY3_SOLVER_OPTION_DEFAULT);
        setOption(Why3_ProblemController::w3opt_vcinject, true);
        setOption(Why3_ProblemController::w3opt_tlim, WHY3_DEFAULT_SOLVER_TLIM);

        setOption(Why3_ProblemController::w3opt_fwdemptexpl, WHY3_DEFAULT_EMPTY_EXPL_FWD_MODE);

        for (const std::pair<std::string, std::string>& hopt : hopts) {
            if (Why3_Opthelpers::is_str_true(hopt.second))
                setOption(hopt.first, true);
            else if (Why3_Opthelpers::is_str_false(hopt.second))
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
