#ifndef LIB_SMTLIB2_CPP_TOOLS__ANNOTATIONS__HEADER
#define LIB_SMTLIB2_CPP_TOOLS__ANNOTATIONS__HEADER

#include <smtlib2tools/smtlib2-defs.hpp>

namespace smtlib2 {

    static const smtannotation_t annot_core_const = "core-const";
    static const smtannotation_t annot_core_magic = "core-magic";

    static const smtannotation_t annot_prepared = "ant-prepared";
    static const smtannotation_t annot_applied = "application-result";

    static const smtannotation_t annot_default = "<?>";

    // static const smtannotation_t <ident> = "";

}

#endif
