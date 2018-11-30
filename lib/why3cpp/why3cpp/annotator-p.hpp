#ifndef LIB_WHY3CPP__ANNOTATOR_HEADER
#define LIB_WHY3CPP__ANNOTATOR_HEADER

#include <memory>
#include <why3cpp/whyml-parser.hpp>

namespace why3cpp {

    namespace whyantlr { class Annotator; }

    class AnnotatorParser : public WhyMLPGeneric {
        std::unique_ptr<whyantlr::Annotator> parser;
    public:
        AnnotatorParser(const std::string& filename);
        ~AnnotatorParser();

        void write(std::ostream& stream);

        bool hasFailed() const;
    };

}

#endif
