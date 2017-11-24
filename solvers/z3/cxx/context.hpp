#ifndef GPID_Z3_CONTEXT_SPP
#define GPID_Z3_CONTEXT_SPP

#include <set>
#include <vector>
#include <z3++.h>

namespace gpid {

    class Z3Declarations {
        z3::sort_vector       sorts;
        z3::func_decl_vector  funs;
        std::vector<z3::expr> todo;
        std::set<unsigned>    seen_ids;

        bool knows_id(unsigned id) const;

        void collect_sort(z3::context& ctx, z3::sort s);
        void collect_fun(z3::context& ctx, z3::func_decl f);
    public:
        Z3Declarations(z3::context& ctx) : sorts(ctx), funs(ctx) {}
        inline z3::sort_vector& getSortDecls() { return sorts; }
        inline z3::func_decl_vector& getFunDecls() { return funs; }

        void collect(z3::context& ctx, z3::expr e);
    };

    struct Z3Hypothesis {
        z3::expr expr;
        Z3Hypothesis(z3::expr e) : expr(e) {}
        Z3Hypothesis(const Z3Hypothesis& e) : expr(e.expr) {}
    };

    struct Z3ModelWrapper {
        const z3::solver& source;
        Z3ModelWrapper(const z3::solver& solver) : source(solver) {}
        Z3ModelWrapper(const Z3ModelWrapper& mdw) : source(mdw.source) {}
        inline bool isSkippable(Z3Hypothesis& h) const {
            return source.get_model().eval(h.expr).bool_value() == Z3_lbool::Z3_L_TRUE;
        }
    };

};

#endif
