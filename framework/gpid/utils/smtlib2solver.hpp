/**
 * \file gpid/utils/smtlib2solver.hpp
 * \brief Generic interface for an SMTLib 2 CLI-compatible SMT Solver
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__UTILS__SMTLIB2_CLI_SOLVER_INTERFACE_HPP
#define GPID_FRAMEWORK__UTILS__SMTLIB2_CLI_SOLVER_INTERFACE_HPP

#include <map>
#include <list>
#include <string>
#include <smtlib2utils/smtlib2utils.hpp>
#include <gpid/core/saitypes.hpp>
#include <gpid/core/memory.hpp>
#include <gpid/utils/abdparseutils.hpp>

namespace gpid {

    struct SMTl2SolverConstraint {
        using constraint_internal = std::shared_ptr<std::string>;
        constraint_internal data;
        SMTl2SolverConstraint() : data(nullptr) {}
        SMTl2SolverConstraint(constraint_internal d) : data(d) {}
        SMTl2SolverConstraint(SMTl2SolverConstraint& o) : data(o.data) {}
    };

    struct SMTl2SolverManager {
        smtlib2utils::SMTl2StringMemory memory;
        std::list<smtlib2utils::SMTl2Command> decls;
    };

    struct SMTl2SolverLiteral {
        using constraint_internal = std::shared_ptr<std::string>;
        constraint_internal data;
        inline std::string str() { return *data; }
        SMTl2SolverLiteral(constraint_internal s) : data(s) {}
        SMTl2SolverLiteral(SMTl2SolverLiteral& o) : data(o.data) {}
    };

    struct SMTl2SolverModel {
        // TODO: See if I can somehow extract the model from it
        inline bool implies(SMTl2SolverLiteral&) const { return false; }
    };

    class SMTl2SolverProblemLoader {
        SMTl2SolverManager ctx;
        SMTl2SolverConstraint curr;
        std::unique_ptr<smtlib2utils::SMTl2CommandParser> parser;
        std::unique_ptr<smtlib2utils::SMTl2CommandHandler> handler;
    public:
        SMTl2SolverProblemLoader();

        inline SMTl2SolverManager& getContextManager() { return ctx; }

        void load(std::string filename, std::string language);
        void prepareReader();

        bool hasConstraint();
        SMTl2SolverConstraint& nextConstraint();
    };

    class SMTl2AbducibleHandler : public AbducibleHandler {
        // SMTl2SolverProblemLoader& pbloader;
        uint32_t _cpt;
        ObjectMapper<SMTl2SolverLiteral>& mapper;
        // std::map<uint32_t, std::list<uint32_t>>& links;
    public:
        SMTl2AbducibleHandler(SMTl2SolverProblemLoader&,
                              ObjectMapper<SMTl2SolverLiteral>& mapper,
                              std::map<uint32_t, std::list<uint32_t>>&)
            : _cpt(0), mapper(mapper) {}

        virtual void allocate(const std::string id, size_t size) override;
        virtual void handleAbducible(const std::shared_ptr<std::string>& abd) override;

        friend class SMTl2SolverAbducibleGenerator;
    };

    class SMTl2SolverAbducibleGenerator {
    public:
        using index_t = typename ObjectMapper<SMTl2SolverLiteral>::index_t;
    private:
        // SMTl2SolverProblemLoader& pbloader;
        ObjectMapper<SMTl2SolverLiteral> mapper;
        std::map<uint32_t, std::list<uint32_t>> links;
        SMTl2AbducibleHandler handler;
    public:
        SMTl2SolverAbducibleGenerator(SMTl2SolverProblemLoader& loader)
            : handler(loader, mapper, links) {}

        void load(std::string filename);
        void generate(std::string generatorid);

        size_t count();

        inline ObjectMapper<SMTl2SolverLiteral>& getMapper() { return mapper; }
        inline std::map<index_t, std::list<index_t>>& getLinks() { return links; }
    };

    class SMTl2SolverInterface {
    public:
        using ContextManagerT = SMTl2SolverManager;
        using LiteralT = SMTl2SolverLiteral;
        using ModelT = SMTl2SolverModel;
        using ProblemLoaderT = SMTl2SolverProblemLoader;
    private:
        const std::string solver_exec;
        ContextManagerT& ctx;

        uint64_t level = 0;
        std::map<uint64_t, std::list<std::shared_ptr<std::string>>> assertions;

        ModelT model;
    public:
        SMTl2SolverInterface(const std::string solver_exec, ContextManagerT& manager)
            : solver_exec(solver_exec), ctx(manager) {}

        inline ContextManagerT& getContextManager() { return ctx; }
        inline ModelT& getModel() { return model; }

        void addConstraint(SMTl2SolverConstraint& cons);
        void addLiteral(LiteralT& lit, bool negate=false);
        template <typename ClauseIteratorGetter> void addClause
        (ClauseIteratorGetter& h, ObjectMapper<LiteralT>& mapper, bool negate=false);

        inline void clearUnsafeClauses() {}

        template<typename ConjunctionIteratorGetter> static std::ostream& write
        (std::ostream& os, ContextManagerT& ctx, ConjunctionIteratorGetter& h,
         ObjectMapper<LiteralT>& mapper, bool negate=false);

        inline void push() { ++level; }
        inline void pop() { assertions[level--].clear(); }

        SolverTestStatus check();

        std::string getPrintableAssertions(bool negate);
    };

    inline void SMTl2SolverInterface::addConstraint(SMTl2SolverConstraint& cons) {
        assertions[level].push_back(cons.data);
    }

    inline void SMTl2SolverInterface::addLiteral(LiteralT& lit, bool negate) {
        if (negate) {
            assertions[level].push_back(ctx.memory.alloc("(not " + lit.str() + ")"));
        } else {
            assertions[level].push_back(lit.data);
        }
    }

    template <typename ClauseIteratorGetter>
    void SMTl2SolverInterface::addClause
    (ClauseIteratorGetter& h, ObjectMapper<LiteralT>& mapper, bool negate) {
        std::stringstream clstr;
        clstr << "(or ";
        auto it = h.begin();
        do {
            if (negate) clstr << "(not ";
            clstr << mapper.get(*it).str();
            if (negate) clstr << ")" ;
        } while (++it != h.end());
        clstr << ")";
        assertions[level].push_back(ctx.memory.alloc(clstr));
    }

    template<typename ConjunctionIteratorGetter>
    std::ostream& SMTl2SolverInterface::write
    (std::ostream& os, ContextManagerT&, ConjunctionIteratorGetter& h,
     ObjectMapper<LiteralT>& mapper, bool negate) {
        if (negate) os << "(not ";
        os << "(and ";
        auto it = h.begin();
        do {
            os << mapper.get(*it).str();
        } while (++it != h.end());
        return negate ? (os << "))") : (os << ")");
    }

}

#endif
