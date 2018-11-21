#define LIB_WHYMLP__EXTRACTOR_CPP

#include <antlr4-runtime.h>
#include <snlog/snlog.hpp>
#include <WhyMLLexer.h>
#include <WhyMLParser.h>
#include <whymlp/extractor-p.hpp>

using namespace std;

#include "error-listener.hpp"
#include "vextract-listener.hpp"

namespace whymlp {
    namespace whyantlr {

        class Extractor {
            const std::string filename;
            map<string, string> vars;
            set<string> refs;
            bool valid;
            bool extracted;
        public:
            Extractor(const std::string& filename);
            ~Extractor();

            inline constexpr bool isValid() const { return valid; }
            inline bool hasExtract() const { return extracted; }

            void extract();

            inline const map<string, string>& getVars() const { return vars; }
            inline const set<string>& getRefs() const { return refs; }
        };

    }
}

void whymlp::whyantlr::Extractor::extract() {
    ifstream source(filename);
    if (source.is_open()) {
        ErrorListener errl(filename);
        antlr4::ANTLRInputStream stream(source);
        WhyMLLexer lexer(&stream);
        lexer.removeErrorListeners();
        lexer.addErrorListener(&errl);
        antlr4::CommonTokenStream tokens(&lexer);
        source.close();

        tokens.fill();

        WhyMLParser parser(&tokens);
        parser.removeParseListeners();
        parser.removeErrorListeners();
        parser.addErrorListener(&errl);
        auto data = parser.mlwfile();

        /* Extract variables */
        antlr4::tree::ParseTreeWalker walker;
        VextractWhyMLListener listener;
        walker.walk(&listener, data);

        vars = listener.getVars();

        for (const pair<string, string>& var : vars)
            if (isRefType(var.second))
                refs.insert(var.first);

        for (const std::string& var : refs)
            vars[var] = asNonRefType(vars[var]);

        /* Conclude */
        valid = !errl.hasDetectedErrors();
    } else {
        valid = false;
    }
    extracted = true;
}

whymlp::whyantlr::Extractor::Extractor(const std::string& filename)
    : filename(filename), valid(true), extracted(false) {}

whymlp::whyantlr::Extractor::~Extractor() {}

whymlp::ExtractorParser::ExtractorParser(const std::string& filename)
    : WhyMLPGeneric(filename), parser(new whyantlr::Extractor(filename)) {}

whymlp::ExtractorParser::~ExtractorParser() {}

bool whymlp::ExtractorParser::hasFailed() const {
    return !parser->isValid();
}

const map<string, string>& whymlp::ExtractorParser::getVars() const {
    if (!parser->hasExtract())
        parser->extract();
    return parser->getVars();
}

const set<string>& whymlp::ExtractorParser::getRefs() const {
    if (!parser->hasExtract())
        parser->extract();
    return parser->getRefs();
}
