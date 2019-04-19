#ifndef LIB_WHY3CPP__LITERALS_GENERATION_PRESET__FROM_WHYML__HEADER
#define LIB_WHY3CPP__LITERALS_GENERATION_PRESET__FROM_WHYML__HEADER

#include <smtlib2tools/literal-generation.hpp>

namespace why3cpp {

    static const smtlib2::smtannotation_t annot_whyml_ref = "whyml-reference";

    const smtlib2::GenerationSet generate_literals_whyml(const std::string& filename);

}

#endif
