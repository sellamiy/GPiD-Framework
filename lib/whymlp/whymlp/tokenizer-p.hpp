#ifndef LIB_WHYMLP__TOKENIZER_HEADER
#define LIB_WHYMLP__TOKENIZER_HEADER

#include <memory>
#include <whymlp/whymlparse.hpp>

namespace whymlp {

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
