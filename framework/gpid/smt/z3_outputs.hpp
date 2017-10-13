#ifndef GPID_Z3_OUTPUT_HANDLING_HPP
#define GPID_Z3_OUTPUT_HANDLING_HPP

#include <iostream>
#include <snlog/snlog.hpp>
#include <gpid/config.hpp>
#include <gpid/smt/z3_engine.hpp>

/* Gpid Z3 integr. output printers */
namespace gpid {

    extern inline
    void p_implicate(std::ostream& out, z3::context& ctx,
                     std::vector<Z3Hypothesis>& impl, bool negate) {
        out << "> ";
        z3::expr pfl = ctx.bool_val(true);;
        for (const Z3Hypothesis hyp : impl) pfl = pfl && hyp.expr;
        if (negate) pfl = !pfl;
        out << pfl << std::endl;
    }

};

#endif
