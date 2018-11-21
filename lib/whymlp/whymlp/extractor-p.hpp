#ifndef LIB_WHYMLP__EXTRACTOR_HEADER
#define LIB_WHYMLP__EXTRACTOR_HEADER

#include <map>
#include <set>
#include <memory>
#include <whymlp/whymlparse.hpp>

namespace whymlp {

    namespace whyantlr { class Extractor; }

    class ExtractorParser : public WhyMLPGeneric {
        std::unique_ptr<whyantlr::Extractor> parser;
    public:
        ExtractorParser(const std::string& filename);
        ~ExtractorParser();

        const std::map<std::string, std::string>& getVars() const;
        const std::map<std::string, std::string>& getLits() const;
        const std::set<std::string>& getRefs() const;

        bool hasFailed() const;
    };

}

#endif
