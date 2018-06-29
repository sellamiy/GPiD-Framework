#ifndef Z3_API_CONTEXT_FOR_GPID__HPP
#define Z3_API_CONTEXT_FOR_GPID__HPP

#include <set>
#include <vector>
#include <z3++.h>

namespace gpid {

    class Z3Declarations {
        z3::context&          ctx;
        z3::sort_vector       sorts;
        z3::func_decl_vector  funs;
        std::vector<z3::expr> todo;
        std::set<unsigned>    seen_ids;

        bool knows_id(unsigned id) const;

        void collect_sort(z3::context& ctx, z3::sort s);
        void collect_fun(z3::context& ctx, z3::func_decl f);
    public:
        using ContextManagerT = z3::context;
        using ConstraintT = z3::expr;
        Z3Declarations(z3::context& ctx) : ctx(ctx), sorts(ctx), funs(ctx) {}
        inline z3::sort_vector& getSortDecls() { return sorts; }
        inline z3::func_decl_vector& getFunDecls() { return funs; }

        void collect(z3::expr e);
    };

    struct Z3Literal {
        z3::expr expr;
        Z3Literal(z3::expr e) : expr(e) {}
        Z3Literal(const Z3Literal& e) : expr(e.expr) {}

        inline const std::string str() const {
            std::stringstream result; result << expr; return result.str();
        }
    };

    struct Z3ModelWrapper {
        const z3::solver& source;
        Z3ModelWrapper(const z3::solver& solver) : source(solver) {}
        Z3ModelWrapper(const Z3ModelWrapper& mdw) : source(mdw.source) {}
        inline bool implies(Z3Literal& h) const {
            return source.get_model().eval(h.expr).bool_value() == Z3_lbool::Z3_L_TRUE;
        }
    };

    inline z3::expr asformula(const z3::expr_vector& v, z3::context& ctx, bool negate=false) {
        z3::expr f(ctx);
        bool finit = false;
        for (unsigned i = 0; i < v.size(); ++i) {
            if (finit)
                f = f && v[i];
            else {
                f = v[i];
                finit = true;
            }
        }
        return negate ? !f : f;
    }

}

#endif
