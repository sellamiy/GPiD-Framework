#ifndef LIB_WHYMLP__ANNOTATOR_HEADER
#define LIB_WHYMLP__ANNOTATOR_HEADER

#include <memory>
#include <whymlp/whymlparse.hpp>

namespace whymlp {

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
