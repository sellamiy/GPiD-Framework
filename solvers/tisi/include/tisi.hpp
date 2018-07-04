/**
 * \file tisi.hpp
 * \brief GPiD Template inactive solver interface for documentation.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef TISI_W_DOC_FOR_GPID__HPP
#define TISI_W_DOC_FOR_GPID__HPP

#include <list>
#include <gpid/core/memory.hpp>
#include <gpid/core/saitypes.hpp>

namespace gpid {

    /**
     * \brief Constraint class.
     *
     * Can be used by the problem loading utility or replaced by any
     * type local to the solver API.
     */
    struct TisiConstraint {};

    /** \brief Context Manager class.
     *
     * Can be used to handle solver global context operations or
     * replaced by the corresponding structure from the solver API.
     */
    struct TisiManager {};

    /**
     * \brief Base class for solver literals.
     *
     * This class represents what is considered a literal by the problem.
     * It will be used by the solver to build formulas.
     */
    struct TisiLiteral {
        /** \return A string representation of this literal. */
        std::string str();
    };

    /**
     * \brief Model wrapper instance for the solver.
     *
     * This class must be provided. If the solver does not provide models,
     * see \ref implies for an appropriate implementation.
     */
    struct TisiModel {
        /**
         * \brief Check if this model entails a given literal.
         *
         * \param lit Literal to check.
         * \return True if lit is a logical consequence of the model.
         * This methods should return false if it is not the case or if
         * this cannot be checked.
         */
        bool implies(TisiLiteral& lit) const;
    };

    /**
     * \brief Input problem loader class.
     *
     * This class implements utilities to load problem instances from files
     * and export it to the Solver interface.
     */
    class TisiProblemLoader {
    public:
        /**
         * \brief Recover the context manager.
         *
         * As the problem loading is the first step in any algorithmic
         * execution in the framework, this class should probably
         * create the context manager.
         * Algorithmic usage of problem loading ensures that the
         * ProblemLoader instance will not be destructed before the end
         * of the execution.
         *
         * \return The context manager used to load the problem.
         */
        TisiManager& getContextManager();

        /**
         * \brief Load a problem from a file.
         *
         * May implement multiple parsers for multiple languages.
         * \param filename Location of the file to load.
         * \param language Expected language of the file.
         */
        void load(std::string filename, std::string language);

        /**
         * \brief Loading preparation.
         *
         * Perform operations required prior to start reading a file.
         */
        void prepareReader();

        /**
         * \brief Export problem constraint.
         *
         * Only called after the problem has been loaded.
         * Check if more constraints can be extracted from the loaded
         * problem.
         * \return True iff more constraints can be extracted.
         */
        bool hasConstraint();

        /**
         * \brief Extract a constraint from the problem.
         *
         * \return The next constraint that can be extracted from the problem.
         * Can only return a constraint once.
         * Correct behavior on call when \ref hasConstraint returns False is
         * not required.
         */
        TisiConstraint& nextConstraint();
    };

    /**
     * \brief Literal generator class.
     *
     * This class implements (abducilbe) literals generation tools.
     * It must provide methods to load literals from an abducible file
     * and may provide additional methods to generate such literals
     * internally.
     */
    class TisiGenerator {
    public:
        /**
         * \brief Build a literal generator for a problem.
         *
         * \param loader Loader of the problem we generate literals for.
         */
        TisiGenerator(TisiProblemLoader& loader);

        /**
         * \brief Load abducible literals from a file.
         *
         * \param filename Location of the file to load.
         * Files are in abd format, use the AbdParser for parsing them.
         */
        void load(std::string filename);

        /**
         * \brief Generate abducible literals for the problem.
         *
         * \param generatorid Internal generation method reference.
         * One can implement as many generation method as wanted.
         */
        void generate(std::string generatorid);

        /**
         * \brief Get the number of literals generated.
         *
         * Can only be called after literals have been generated via a call
         * to \ref load or \ref generate.
         * \return The number of literals that have been read/generated.
         */
        size_t count();

        /**
         * \brief Get the literal referencer.
         *
         * Literals generated are stored in memory. Further access is made
         * by reference through an ObjectMapper that is constructed by this
         * generated. See its documentation for more details.
         * \return The object mapper for the generated literals.
         */
        ObjectMapper<TisiLiteral>& getMapper();
        /** Generated literal reference type. */
        using index_t = typename ObjectMapper<TisiLiteral>::index_t;

        /**
         * \brief Literal linkage information.
         *
         * Literals may be linked to others.
         * \return Literal linkage information.
         */
        std::map<index_t, std::list<index_t>>& getLinks();
    };

    /**
     * \brief Main solver interface class.
     *
     * This class acts as a wrapper to a solver instance.
     * Each interface must be independent from the other.
     */
    class TisiInterface {
    public:
        /** Interface context management type */
        using ContextManagerT = TisiManager;
        /** Interface literal type */
        using LiteralT = TisiLiteral;
        /** Interface model type */
        using ModelT = TisiModel;
        /** Interface problem loader type */
        using ProblemLoaderT = TisiProblemLoader;

        /**
         * \brief Initialize an interface.
         *
         * \param manager Context manager to use for the solver instance.
         */
        TisiInterface(ContextManagerT& manager);

        /** \return The underlying context manager. */
        ContextManagerT& getContextManager();
        /**
         * \brief Get the current model.
         *
         * The model is only relevant if the last \ref check call returned SAT.
         * Specific behavior when called in any other state is not required.
         * A model returned by this method is not required to remain valid
         * after the next \ref check call.
         * \return A model of the current problem.
         * See also the TisiModel call documentation.
         */
        ModelT& getModel();

        /**
         * \brief Add a constraint to the solver.
         *
         * Constraints are expected to stay in the solver.
         * \param cons Constraint to add.
         */ 
        void addConstraint(TisiConstraint& cons);

        /**
         * \brief Add a literal to the solver.
         *
         * The literal is added as a constraint in the current level context
         * (see \ref push, \ref pop).
         * \param lit Literal to add.
         * \param negate If true, add the negation of the literal instead.
         */
        void addLiteral(LiteralT& lit, bool negate=false);

        /**
         * \brief Add a clause to the solver.
         *
         * The clause is added as a constraint in the current level context
         * (see \ref push, \ref pop).
         * \param h Clause iterator getter : object with begin and end methods
         * returning iterators on Literal references (ObjectMapper<LiteralT>::index_t).
         * Literal iteration represents a clause (disjunction).
         * \param mapper Mapper from literal references to actual literals.
         * \param negate If true, add the negation of the clause instead.
         */
        template<typename ClauseIteratorGetter>
        void addClause(ClauseIteratorGetter& h, ObjectMapper<LiteralT>& mapper,
                       bool negate=false);

        /**
         * \brief Remove clauses that have been added below depth 0.
         *
         * This should remove from the solver all clauses that have not been
         * added at the top level.
         * \deprecated A well-made solver interface should not require this
         * as push-pop should perform such tasks. If push and pop are not
         * able to remove clauses, implement this method to do so.
         * In any other cases, this method should do nothing.
         */
        void clearUnsafeClauses();

        /**
         * \brief Write literals to stream.
         *
         * This method is used to print this solver's literals correctly.
         * \param os Stream to write to.
         * \param ctx Context manager for writing literals.
         * \param h Conjunction iterator getter : object with begin and end
         * methods returning iterators on Literal references
         * (ObjectMapper<LiteralT>::index_t). Literal iteration represents
         * a conjunction.
         * \param mapper Mapper from literal references to actual literals.
         * \param negate If true, print the negation of the conjunction instead.
         * \return os after writing the literals to it.
         */
        template<typename ConjunctionIteratorGetter>
        static std::ostream& write(std::ostream& os, ContextManagerT& ctx,
                                   ConjunctionIteratorGetter& h,
                                   ObjectMapper<LiteralT>& mapper, bool negate=false);

        /**
         * \brief Push the solver contextual level.
         *
         * Any literal or clause added after a push will be linked to this
         * contextual level. After doing a \ref pop on this level, such
         * literals/clauses will be removed from the solver.
         * Constraints are not affected by the contextual level.
         */
        void push();
        /** Pop the solver contextual level. Ses also \ref push. */
        void pop();

        /**
         * \brief Check the current assertions satisfiability status.
         *
         * \return SolverTestStatus::SAT if the current assertions are
         * satisfiable, SolverTestStatus::UNSAT if they are unsatisfiable
         * and SolverTestStatus::UNKNOWN if the solver cannot answer
         * the query.
         */
        SolverTestStatus check();

        /**
         * \brief Get a string representation of the current assertions.
         *
         * \return A string representation of the assertions at the current
         * contextual level.
         * \note This is only required if the framework has been compiled
         * with the instrumentation tools on.
         */
        std::string getPrintableAssertions(bool negate); // instru
    };

    template<typename ClauseIteratorGetter>
    void TisiInterface::addClause(ClauseIteratorGetter&, ObjectMapper<LiteralT>&, bool) {}

    template<typename ConjunctionIteratorGetter>
    std::ostream& TisiInterface::write
    (std::ostream& os, ContextManagerT&, ConjunctionIteratorGetter&, ObjectMapper<LiteralT>&, bool)
    { return os << "*_*"; }

}

#endif
