#ifndef LIB_WHY3CPP__LITERALS_GENERATION_PRESET__FROM_WHYML__HEADER
#define LIB_WHY3CPP__LITERALS_GENERATION_PRESET__FROM_WHYML__HEADER

#include <smtlib2tools/smtlit-generation.hpp>

namespace why3cpp {

    const smtlib2::GenerationSet generate_literals_whyml(const std::string& filename);

}

#endif
