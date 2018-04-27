#ifndef GPID_Z3_EXPR_STORAGE_HPP
#define GPID_Z3_EXPR_STORAGE_HPP


#include <ugly/ugly.hpp>

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

    class Z3EntailmentChecker {
        z3::solver solver;
    protected:
        inline bool entailment_check(z3::expr source, z3::expr target) {
            solver.push();
            solver.add(source);
            solver.add(!target);
            z3::check_result qres = solver.check();
            solver.pop();
            switch (qres) {
            case z3::sat:   return false;
            case z3::unsat: return true;
            default:
                throw LocalZ3ExpressionStorageException("Z3 Entailment test returned Unknown");
                return false;
            }
        }
    public:
        Z3EntailmentChecker(z3::context& ctx) : solver(ctx) {}
    };

    struct Z3StorageRefuser : public Z3EntailmentChecker {
        inline bool operator()(z3::expr insert, z3::expr other) {
            return entailment_check(other, insert);
        }
        Z3StorageRefuser(z3::context& ctx) : Z3EntailmentChecker(ctx) {}
    };

    struct Z3StorageCleaner : public Z3EntailmentChecker {
        inline bool operator()(z3::expr insert, z3::expr other) {
            return entailment_check(insert, other);
        }
        Z3StorageCleaner(z3::context& ctx) : Z3EntailmentChecker(ctx) {}
    };

    class Z3Storage {
        typedef ugly::BeurkTable<z3::expr, Z3StorageRefuser, Z3StorageCleaner> Z3BTable;
        Z3BTable btable;
    public:
        Z3Storage(z3::context& ctx) : btable(ctx) {}
        inline void insert(z3::expr e) {
            btable.insert_refuse_clean(e);
        }
        inline bool would_be_inserted(z3::expr e) {
            return btable.dry_insert_refuse(e);
        }
        typedef Z3BTable::iterator iterator;
        typedef Z3BTable::const_iterator const_iterator;
        inline iterator begin() { return btable.begin(); }
        inline iterator end()   { return btable.end(); }
        inline const_iterator cbegin() { return btable.cbegin(); }
        inline const_iterator cend()   { return btable.cend(); }
    };

}

#endif
