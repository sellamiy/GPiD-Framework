/**
 * \file smtlib2tools/types-core.hpp
 * \brief Minimal smtlib2 type definitions.
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_SMTLIB2_CPP_TOOLS__TYPES_CORE__HEADER
#define LIB_SMTLIB2_CPP_TOOLS__TYPES_CORE__HEADER

#include <smtlib2tools/core.hpp>

namespace smtlib2 {

    static const smttype_t smt_bool = "Bool";
    static const smttype_t smt_int = "Int";
    static const smttype_t smt_real = "Real";

    static const smttype_t smt_anytype = "'?*";

    // static const smttype_t <ident> = "";

}

#endif
