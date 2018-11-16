#ifndef LIB_WHYMLP__PARSERS_CORE_DEFS_HEADER
#define LIB_WHYMLP__PARSERS_CORE_DEFS_HEADER

#include <string>

namespace whymlp {

    class WhyMLPGeneric {
        const std::string filename;
    protected:
        inline const std::string& sourcefile() const { return filename; }
    public:
        WhyMLPGeneric(const std::string& filename) : filename(filename) {}
    };

}

#endif
