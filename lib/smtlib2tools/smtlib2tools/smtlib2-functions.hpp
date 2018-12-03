#ifndef LIB_SMTLIB2_CPP_TOOLS__FUNCTIONS__HEADER
#define LIB_SMTLIB2_CPP_TOOLS__FUNCTIONS__HEADER

#include <smtlib2tools/smtlib2-types.hpp>

namespace smtlib2 {

    static const smtfun_t smt_and_f = smtfun_t("and", smt_bool, { smt_bool, smt_bool });
    static const smtfun_t smt_or_f =  smtfun_t("or",  smt_bool, { smt_bool, smt_bool });
    static const smtfun_t smt_not_f = smtfun_t("not", smt_bool, { smt_bool });

    static inline const smtfun_t smt_eq_f(const smttype_t& type)
    { return smtfun_t("=", smt_bool, { type, type }); }
    static inline const smtfun_t smt_neq_f(const smttype_t& type)
    { return smtfun_t("distinct", smt_bool, { type, type }); }
    static inline const smtfun_t smt_leq_f(const smttype_t& type)
    { return smtfun_t("<=", smt_bool, { type, type }); }
    static inline const smtfun_t smt_geq_f(const smttype_t& type)
    { return smtfun_t(">=", smt_bool, { type, type }); }
    static inline const smtfun_t smt_lt_f(const smttype_t& type)
    { return smtfun_t("<", smt_bool, { type, type }); }
    static inline const smtfun_t smt_gt_f(const smttype_t& type)
    { return smtfun_t(">", smt_bool, { type, type }); }

    static const smtfun_t smt_mod_f = smtfun_t("mod", smt_int, { smt_int, smt_int });

    // static const smtfun_t <ident> = smtfun_t("ident", "rtype", { "param1", "param2" });

}

#endif
