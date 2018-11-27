#define LIB_WHYMLP__ANNOTATOR_CPP

#include <snlog/snlog.hpp>
#include <WhyMLLexer.h>
#include <WhyMLParser.h>
#include <whymlp/annotator-p.hpp>

using namespace std;

#include "error-listener.hpp"

namespace whymlp {
    namespace whyantlr {

        class Annotator {
            antlr4::ANTLRInputStream* stream;
            antlr4::CommonTokenStream* tokens;
            WhyMLLexer* lexer;
            WhyMLParser* parser;
            antlr4::tree::ParseTree* data;
            bool valid;
        public:
            Annotator(const std::string& filename);
            ~Annotator();

            inline constexpr bool isValid() const { return valid; }

            void annotate(std::ostream& output);
        };

    }
}

whymlp::whyantlr::Annotator::Annotator(const std::string& filename) {
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

        parser = new WhyMLParser(tokens);
        parser->removeParseListeners();
        parser->removeErrorListeners();
        parser->addErrorListener(&errl);
        data = parser->mlwfile();

        valid = !errl.hasDetectedErrors();
    } else {
        valid = false;
    }
}

whymlp::whyantlr::Annotator::~Annotator() {
    if (parser != nullptr) delete parser;
    if (tokens != nullptr) delete tokens;
    if (lexer  != nullptr) delete lexer;
    if (stream != nullptr) delete stream;
}

void whymlp::whyantlr::Annotator::annotate(std::ostream& output) {
    if (isValid()) output << data->toStringTree(parser) << endl;
    else snlog::l_error() << "Annotator used after parse error" << snlog::l_end;
}

whymlp::AnnotatorParser::AnnotatorParser(const std::string& filename)
    : WhyMLPGeneric(filename), parser(new whyantlr::Annotator(filename)) {}

whymlp::AnnotatorParser::~AnnotatorParser() {}

bool whymlp::AnnotatorParser::hasFailed() const {
    return !parser->isValid();
}

void whymlp::AnnotatorParser::write(std::ostream& stream) {
    parser->annotate(stream);
}
