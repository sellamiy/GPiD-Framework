#ifndef LIB_WHYMLP__VARIABLES_EXTRACTOR_HEADER
#define LIB_WHYMLP__VARIABLES_EXTRACTOR_HEADER

#include <map>
#include <set>
#include <memory>
#include <whymlp/whymlparse.hpp>

namespace whymlp {

    namespace whyantlr { class Vextractor; }

    class VextractParser : public WhyMLPGeneric {
        std::unique_ptr<whyantlr::Vextractor> parser;
    public:
        VextractParser(const std::string& filename);
        ~VextractParser();

        const std::map<std::string, std::string>& getVars() const;
        const std::set<std::string>& getRefs() const;

        bool hasFailed() const;
    };

}

#endif
