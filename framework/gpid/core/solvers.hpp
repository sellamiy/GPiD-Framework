/**
 * \file gpid/core/solvers.hpp
 * \brief GPiD-Framework Solver interfaces elements.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__SOLVERS_HPP
#define GPID_FRAMEWORK__CORE__SOLVERS_HPP

#include <gpid/config.hpp>
#include <gpid/core/wrappers.hpp>

namespace gpid {

    /** \brief Generic Wrapper for Solver test results. \ingroup gpidcorelib */
    enum class SolverTestStatus {
        /** The formula is satisfiable */
        SAT,
        /** The formula is unsatisfiable */
        UNSAT,
        /** The formula satisfiability status cannot be computed */
        UNKNOWN
    };
    inline std::string to_string(const SolverTestStatus& s)
    { return s == SolverTestStatus::SAT ?
            "SAT" : s == SolverTestStatus::UNSAT ? "UNSAT" : "UNKNOWN"; }

    template<class CContextManagerT, class CLiteralT, class CModelT>
    class AbstractSolverInterface {
    public:
        typedef CContextManagerT ContextManagerT;
        typedef CLiteralT LiteralT;
        typedef CModelT ModelT;
        typedef LiteralHypothesis<LiteralT> HypothesisT;
        virtual void push() = 0;
        virtual void pop() = 0;
        virtual void addLiteral(LiteralT& lit, bool negate) = 0;
        virtual void addClause(HypothesisT& h, LiteralMapper<LiteralT>& mapper, bool negate) = 0;
        virtual SolverTestStatus check() = 0;
        virtual ModelT& getModel() = 0;

        virtual void printAssertions(bool negated=false) = 0;
        virtual const std::string getPrintableAssertions(bool negated=false) = 0;
    protected:
        ContextManagerT& ctx;
        AbstractSolverInterface(ContextManagerT& ctx) : ctx(ctx) {}
    };

    template<class CInterfaceT, class CProblemT, class CDeclarationsT>
    class AbstractSolverEngine {
    public:
        typedef CInterfaceT InterfaceT;
        typedef CProblemT ProblemT;
        typedef CDeclarationsT DeclarationsT;
        typedef typename InterfaceT::LiteralT LiteralT;
        typedef typename InterfaceT::ModelT ModelT;
        typedef typename InterfaceT::ContextManagerT ContextManagerT;
        typedef uint32_t level_t;
    private:
        std::vector<InterfaceT*> _interfaces;
    protected:
        ContextManagerT ctx;

        level_t c_level;

        typedef uint32_t interface_id_t;
        inline interface_id_t createInterface() {
            interface_id_t nid = _interfaces.size();
            _interfaces.push_back(new InterfaceT(ctx));
            return nid;
        }
        inline InterfaceT& getInterface(interface_id_t id) const {
            return *(_interfaces[id]);
        }

        const interface_id_t problemInterfaceId;
        const interface_id_t consistencyInterfaceId;

        inline void accessLevel(level_t level) {
            while (level > c_level) {
                getInterface(problemInterfaceId).push();
                getInterface(consistencyInterfaceId).push();
                c_level++;
            }
            while (level < c_level) {
                getInterface(problemInterfaceId).pop();
                getInterface(consistencyInterfaceId).pop();
                c_level--;
            }
        }

        AbstractSolverEngine()
            : problemInterfaceId(createInterface()), consistencyInterfaceId(createInterface())
        { }
    public:

        inline InterfaceT& additionalInterface() {
            return getInterface(createInterface());
        }

        inline ContextManagerT& getContextManager() { return ctx; }
        inline level_t getLevel() { return c_level; }

        
        /** \brief Display basic information on the solver used */
        virtual void printInfos() = 0;
        virtual void setProblem(ProblemT& problem) = 0;
        virtual void start() = 0;

        inline ModelT& recoverModel() {
            return getInterface(problemInterfaceId).getModel();
        }

        /** \brief String representation of the current literals set */
        inline const std::string hypothesisAsString() const {
            return getInterface(consistencyInterfaceId).getPrintableAssertions(false);
        }
        /** \brief Print the current set of literals */
        inline void printHypothesis() {
            getInterface(consistencyInterfaceId).printAssertions();
        }
        /** \brief Print the negation of the current set of literals */
        inline void printHypothesisNegation() {
            getInterface(consistencyInterfaceId).printAssertions(true);
        }

        /** \brief Remove all the literals assigned after a given level */
        inline void removeLiterals(level_t level) {
            accessLevel(level - 1);
            accessLevel(level);
        }
        /** \brief Add an abducible literal to the solver */
        inline void addLiteral(LiteralT& literal, level_t level) {
            accessLevel(level);
            getInterface(problemInterfaceId).addLiteral(literal);
            getInterface(consistencyInterfaceId).addLiteral(literal);
        }
        /** \brief Check if the current set of literals is compatible with the problem */
        inline SolverTestStatus testHypothesis(level_t level) {
            accessLevel(level);
            return getInterface(problemInterfaceId).check();
        }
        /** \brief Check if the current set of literals is self-consistent */
        inline SolverTestStatus checkConsistency(level_t level) {
            accessLevel(level);
            return getInterface(consistencyInterfaceId).check();
        }
        /** \brief Check if an literal is already a consequence of the current state */
        inline bool isConsequence(LiteralT&, level_t) {
            snlog::l_warn("isConsequence not available in the version ***heavy devel");
            return false;
        }
    };

}

#endif
