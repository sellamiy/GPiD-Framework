#ifndef LIB_WHY3CPP__PARSERS_CORE_DEFS_HEADER
#define LIB_WHY3CPP__PARSERS_CORE_DEFS_HEADER

#include <string>

namespace why3cpp {

    class WhyMLPGeneric {
        const std::string filename;
    protected:
        inline const std::string& sourcefile() const { return filename; }
    public:
        WhyMLPGeneric(const std::string& filename) : filename(filename) {}
    };

}

#endif
