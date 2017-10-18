#ifndef GPID_Z3_CONTEXT_HPP
#define GPID_Z3_CONTEXT_HPP

#include <set>
#include <vector>
#include <z3++.h>

namespace gpid {

    class Z3Declarations {
        std::vector<std::string>   names;
        std::vector<z3::sort>      sorts;
        std::vector<z3::func_decl> funs;
        std::vector<z3::expr>      todo;
        std::set<unsigned>         seen_ids;

        bool knows_id(unsigned id) const;

        void collect_sort(z3::context& ctx, z3::sort s);
        void collect_fun(z3::context& ctx, z3::func_decl f);
    public:
        void collect(z3::context& ctx, z3::expr e);

    };

};

#endif
