#ifndef LIB_WHY3CPP__TOKENIZER_HEADER
#define LIB_WHY3CPP__TOKENIZER_HEADER

#include <memory>
#include <why3cpp/whyml-parser.hpp>

namespace why3cpp {

    namespace whyantlr { class TokenizerAnt; }

    class Tokenizer : public WhyMLPGeneric {
        std::unique_ptr<whyantlr::TokenizerAnt> parser;
    public:
        Tokenizer(const std::string& filename);
        ~Tokenizer();

        void write(std::ostream& stream);

        bool hasFailed() const;
    };

}

#endif
