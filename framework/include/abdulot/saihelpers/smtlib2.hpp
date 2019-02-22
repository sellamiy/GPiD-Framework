/**
 * \file abdulot/saihelpers/smtlib2.hpp
 * \brief Generic interface for an SMTLib 2 CLI-compatible SMT Solver
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__SAI_HELPERS__SMTLIB2_CLI_SOLVER_INTERFACE_HPP
#define ABDULOT__SAI_HELPERS__SMTLIB2_CLI_SOLVER_INTERFACE_HPP

#include <smtlib2tools/parser-command.hpp>
#include <abdulot/core/saitypes.hpp>
#include <abdulot/core/memory.hpp>
#include <abdulot/utils/abducibles-utils.hpp>

namespace abdulot {
namespace saihelpers {

    struct SMTl2SolverConstraint {
        using constraint_internal = std::shared_ptr<std::string>;
        constraint_internal data;
        SMTl2SolverConstraint() : data(nullptr) {}
        SMTl2SolverConstraint(constraint_internal d) : data(d) {}
        SMTl2SolverConstraint(SMTl2SolverConstraint& o) : data(o.data) {}
    };

    struct SMTl2SolverManager {
        smtlib2::StringMemory memory;
        std::list<smtlib2::SMTl2Command> opts;
        std::list<smtlib2::SMTl2Command> decls;
    };

    struct SMTl2SolverLiteral {
        using constraint_internal = std::shared_ptr<std::string>;
        constraint_internal data;
        inline std::string str() { return *data; }
        SMTl2SolverLiteral(constraint_internal s) : data(s) {}
        SMTl2SolverLiteral(const SMTl2SolverLiteral& o) : data(o.data) {}
    };

    struct SMTl2SolverModel {
        // TODO: See if I can somehow extract the model from it
        inline bool implies(SMTl2SolverLiteral&) const { return false; }
    };

    class SMTl2SolverProblemLoader {
        SMTl2SolverManager ctx;
        SMTl2SolverConstraint curr;
        std::unique_ptr<smtlib2::SMTl2CommandParser> parser;
        std::unique_ptr<smtlib2::SMTl2CommandHandler> handler;
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
        virtual void handleAbducible(const std::string& abd) override;

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
        struct TimeoutData { const std::string cliopt; const uint32_t factor; };
    private:
        const std::string solver_exec;
        ContextManagerT& ctx;
        const SolverInterfaceOptions& siopts;
        const TimeoutData tdata;

        const std::string script_file;

        uint64_t level = 0;
        std::map<uint64_t, std::list<std::shared_ptr<std::string>>> assertions;

        ModelT model;
    public:
        SMTl2SolverInterface(const std::string& solver_exec, ContextManagerT& manager,
                             const SolverInterfaceOptions& siopts,
                             const std::string& to_cliopt, uint32_t to_factor)
            : solver_exec(solver_exec), ctx(manager), siopts(siopts), tdata({ to_cliopt, to_factor }),
              script_file("_ssivc_gpid_temp_" + std::to_string((uintptr_t)this) + ".smt2")
        {}

        inline ContextManagerT& getContextManager() { return ctx; }
        inline ModelT& getModel() { return model; }

        void addConstraint(SMTl2SolverConstraint& cons);
        void addLiteral(LiteralT& lit, bool negate=false);
        template <typename ClauseIteratorGetter> void addClause
        (ClauseIteratorGetter& h, ObjectMapper<LiteralT>& mapper, bool negate=false);

        inline void clearUnsafeClauses() {}

        template<typename ConjunctionIteratorGetter> static std::ostream& write
        (std::ostream& os, ContextManagerT& ctx, ConjunctionIteratorGetter& h,
         const ObjectMapper<LiteralT>& mapper, bool negate=false);

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
     const ObjectMapper<LiteralT>& mapper, bool negate) {
        if (negate) os << "(not ";
        os << "(and ";
        auto it = h.begin();
        do {
            os << mapper.get(*it).str();
        } while (++it != h.end());
        return negate ? (os << "))") : (os << ")");
    }

}
}

#endif
