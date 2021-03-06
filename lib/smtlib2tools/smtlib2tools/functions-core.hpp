/**
 * \file smtlib2tools/functions-core.hpp
 * \brief Minimal smtlib2 function definitions.
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_SMTLIB2_CPP_TOOLS__FUNCTIONS_CORE__HEADER
#define LIB_SMTLIB2_CPP_TOOLS__FUNCTIONS_CORE__HEADER

#include <smtlib2tools/types-core.hpp>

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

    static inline const smtfun_t smt_plus_f(const smttype_t& type)
    { return smtfun_t("+", type, { type, type }); }
    static inline const smtfun_t smt_mult_f(const smttype_t& type)
    { return smtfun_t("*", type, { type, type }); }

    // static const smtfun_t <ident> = smtfun_t("ident", "rtype", { "param1", "param2" });

}

#endif
