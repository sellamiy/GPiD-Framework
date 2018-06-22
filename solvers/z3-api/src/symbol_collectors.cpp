#define Z3_API_INTERFACE_FOR_GPID__SYMBOL_COLLECTORS__CPP

#include <z3-api-context.hpp>

/* Strongly inspired from z3/examples/tptp/tptp5.cpp */
/* See also:
   https://stackoverflow.com/questions/39882992/how-to-get-the-declaration-from-a-z3-smtlib2-formula */

inline bool gpid::Z3Declarations::knows_id(unsigned id) const {
    return seen_ids.find(id) != seen_ids.end();
}

inline void gpid::Z3Declarations::collect_sort(z3::context& ctx, z3::sort s) {
    unsigned id = Z3_get_sort_id(ctx, s);
    if (s.sort_kind() == Z3_UNINTERPRETED_SORT && 
        knows_id(id)) { // TODO : Understand why this should work
        seen_ids.insert(id);
        sorts.push_back(s);
    }
}

inline void gpid::Z3Declarations::collect_fun(z3::context& ctx, z3::func_decl f) {
    unsigned id = Z3_get_func_decl_id(ctx, f);
    if (knows_id(id)) return;
    seen_ids.insert(id);
    if (f.decl_kind() == Z3_OP_UNINTERPRETED) {
        funs.push_back(f);
    }
    for (unsigned i = 0; i < f.arity(); ++i) {
        collect_sort(ctx, f.domain(i));
    }
    collect_sort(ctx, f.range());
}

void gpid::Z3Declarations::collect(z3::context& ctx, z3::expr e) {
    todo.push_back(e);
    while (!todo.empty()) {

        z3::expr e = todo.back();
        todo.pop_back();

        unsigned id = Z3_get_ast_id(ctx, e);
        if (knows_id(id)) continue;
        seen_ids.insert(id);

        if (e.is_app()) {
            collect_fun(ctx, e.decl());
            unsigned sz = e.num_args();
            for (unsigned i = 0; i < sz; ++i) {
                todo.push_back(e.arg(i));
            }
        }
        else if (e.is_quantifier()) {
            unsigned nb = Z3_get_quantifier_num_bound(e.ctx(), e);
            for (unsigned i = 0; i < nb; ++i) {
                z3::sort srt(ctx, Z3_get_quantifier_bound_sort(e.ctx(), e, i));
                collect_sort(ctx, srt);
            }
            todo.push_back(e.body());
        }
        else if (e.is_var()) {
            collect_sort(ctx, e.get_sort());
        }
    }
}
