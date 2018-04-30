#ifndef GPID_Z3_EXPR_STORAGE_HPP
#define GPID_Z3_EXPR_STORAGE_HPP

#include <gpid/util/storage.hpp>

namespace gpid {

    /** \brief Main exception class for the framework related errors */
    class LocalZ3ExpressionStorageException : public std::exception {
        std::string reason;
    public:
        LocalZ3ExpressionStorageException(std::string reason) : reason(reason) { }
        virtual const char* what() const throw () {
            return reason.c_str();
        }
    };

    class Z3StorageSolverWrapper {
        z3::solver solver;
    public:
        Z3StorageSolverWrapper(z3::context& ctx) : solver(ctx) { }

        inline void push() { solver.push(); }
        inline void pop() { solver.pop(); }

        inline void addFormula(z3::expr f, bool negate) {
            solver.add(negate ? !f : f);
        }

        inline SolverTestStatus check() {
            z3::check_result qres = solver.check();
            switch (qres) {
            case z3::sat:   return SolverTestStatus::SOLVER_SAT;
            case z3::unsat: return SolverTestStatus::SOLVER_UNSAT;
            default:        return SolverTestStatus::SOLVER_UNKNOWN;
            }
        }
    };

    class Z3StorageLiteral {
        static std::map<std::string, uint32_t> ordermap;
        static uint32_t corder_value;
        static uint32_t next_ovalue() { return ++corder_value; }
    public:
        z3::expr e;
        Z3StorageLiteral(z3::expr e) : e(e) { }
        Z3StorageLiteral(const Z3StorageLiteral& o) : e(o.e) { }

        bool operator < (const Z3StorageLiteral& o) const {
            std::stringstream sselfstr, sostr;
            std::string selfstr, ostr;
            sselfstr << e;
            sostr << o.e;
            selfstr = sselfstr.str();
            ostr = sostr.str();
            if (ordermap.find(selfstr) == ordermap.end())
                ordermap[selfstr] = next_ovalue();
            if (ordermap.find(ostr) == ordermap.end())
                ordermap[ostr] = next_ovalue();
            return ordermap[selfstr] < ordermap[ostr];
        }
    };

    class Z3StorageUtils {
        z3::context& ctx;
    public:
        Z3StorageUtils(z3::context& ctx) : ctx(ctx) { }

        typedef Z3StorageLiteral LiteralT;
        typedef z3::expr FormulaT;
        typedef Z3StorageSolverWrapper SolverT;
        typedef z3::expr_vector LiteralListT;

        inline FormulaT negation(FormulaT e) const { return !e; }
        inline FormulaT disjunction(FormulaT l, FormulaT r) const
        /* TODO: Find a cleaner and more efficient way to test if l is null */
        { return (l.to_string() == "null") ? r : l || r; }
        inline FormulaT emptyFormula() const { return FormulaT(ctx); }
        inline FormulaT toFormula(LiteralT l, bool negate=false) const
        { return negate ? !(l.e) : l.e; }
        inline FormulaT toFormula(LiteralListT ll, bool negate) const
        { return asformula(ll, ctx, negate); }
        inline void printImplicate(FormulaT f) const
        { p_implicate(std::cout, f, false); }
    };

    class Z3Storage {
        typedef AbducibleTree<Z3StorageUtils> Z3ATree;
        Z3ATree atree;
    public:
        Z3Storage(z3::context& ctx) : atree(ctx) {}
        inline void insert(const z3::expr_vector& i, z3::expr e, bool negate) {
            atree.cleanSubsumed(e, negate);
            atree.insert(i, negate);
        }
        inline bool would_be_inserted(z3::expr e)
        { return !atree.subsumes(e); }
        inline void print()
        { atree.print(); }
    };

}

#endif
