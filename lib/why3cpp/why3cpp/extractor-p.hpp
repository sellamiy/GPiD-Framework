#ifndef LIB_WHY3CPP__EXTRACTOR_HEADER
#define LIB_WHY3CPP__EXTRACTOR_HEADER

#include <map>
#include <set>
#include <list>
#include <vector>
#include <memory>
#include <why3cpp/whyml-parser.hpp>

namespace why3cpp {

    namespace whyantlr { class Extractor; }

    class ExtractorParser : public WhyMLPGeneric {
        std::unique_ptr<whyantlr::Extractor> parser;
    public:
        ExtractorParser(const std::string& filename);
        ~ExtractorParser();

        const std::map<std::string, std::string>& getVars() const;
        const std::map<std::string, std::string>& getLits() const;
        const std::set<std::string>& getRefs() const;
        const std::map<std::string, std::list<std::vector<std::string>>>& getAppls() const;

        bool hasFailed() const;
    };

}

#endif
