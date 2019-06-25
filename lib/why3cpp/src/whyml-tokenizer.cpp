#define LIB_WHY3CPP__TOKENIZER_CPP

#include <snlog/snlog.hpp>
#include <WhyMLLexer.h>
#include <why3cpp/whyml-tokenizer.hpp>

using namespace std;

#include "whyml-error-listener.hpp"

namespace why3cpp {
    namespace whyantlr {

        class TokenizerAnt {
            antlr4::ANTLRInputStream* stream;
            antlr4::CommonTokenStream* tokens;
            WhyMLLexer* lexer;
            bool valid;
        public:
            TokenizerAnt(const std::string& filename);
            ~TokenizerAnt();

            inline bool isValid() const { return valid; }

            void tokenize(std::ostream& output);
        };

    }
}

why3cpp::whyantlr::TokenizerAnt::TokenizerAnt(const std::string& filename) {
    ifstream source(filename);
    if (source.is_open()) {
        ErrorListener errl(filename);
        stream = new antlr4::ANTLRInputStream(source);
        lexer = new WhyMLLexer(stream);
        lexer->removeErrorListeners();
        lexer->addErrorListener(&errl);
        tokens = new antlr4::CommonTokenStream(lexer);
        source.close();

        tokens->fill();

        valid = !errl.hasDetectedErrors();
    } else {
        valid = false;
    }
}

why3cpp::whyantlr::TokenizerAnt::~TokenizerAnt() {
    if (tokens != nullptr) delete tokens;
    if (lexer  != nullptr) delete lexer;
    if (stream != nullptr) delete stream;
}

void why3cpp::whyantlr::TokenizerAnt::tokenize(std::ostream& output) {
    if (isValid())
        for(auto tk : tokens->getTokens())
            output << "-- " << tk->toString() << std::endl;
    else snlog::l_error() << "Annotator used after parse error" << snlog::l_end;
}

why3cpp::Tokenizer::Tokenizer(const std::string& filename)
    : WhyMLPGeneric(filename), parser(new whyantlr::TokenizerAnt(filename)) {}

why3cpp::Tokenizer::~Tokenizer() {}

bool why3cpp::Tokenizer::hasFailed() const {
    return !parser->isValid();
}

void why3cpp::Tokenizer::write(std::ostream& stream) {
    parser->tokenize(stream);
}
