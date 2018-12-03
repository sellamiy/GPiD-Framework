#define LIB_WHY3CPP__EXTRACTOR_CPP

#include <snlog/snlog.hpp>
#include <ugly/Mfff.hpp>
#include <WhyMLLexer.h>
#include <why3cpp/extractor-p.hpp>

using namespace std;

#include "error-listener.hpp"
#include "vextract-listener.hpp"
#include "lextract-listener.hpp"
#include "aplextract-listener.hpp"

namespace why3cpp {
    namespace whyantlr {

        class Extractor {
            const std::string filename;
            map<string, string> vars;
            map<string, string> lits;
            set<string> refs;
            map<string, list<vector<string>>> appls;
            bool valid;
            bool extracted;
        public:
            Extractor(const std::string& filename);
            ~Extractor();

            inline constexpr bool isValid() const { return valid; }
            inline bool hasExtract() const { return extracted; }

            void extract();

            inline const map<string, string>& getVars() const { return vars; }
            inline const map<string, string>& getLits() const { return lits; }
            inline const set<string>& getRefs() const { return refs; }
            inline const map<string, list<vector<string>>>& getAppls() const { return appls; }
        };

    }
}

void why3cpp::whyantlr::Extractor::extract() {
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

        antlr4::tree::ParseTreeWalker walker;

        /* Extract variables */
        VextractWhyMLListener vlistener;
        walker.walk(&vlistener, data);

        vars = vlistener.getVars();

        for (const pair<string, string>& var : vars)
            if (isRefType(var.second))
                refs.insert(var.first);

        for (const std::string& var : refs)
            vars[var] = asNonRefType(vars[var]);

        /* Extract constants */
        LextractWhyMLListener llistener;
        walker.walk(&llistener, data);

        lits = llistener.getLiterals();

        /* Extract applications */
        AplextractWhyMLListener aplistener;
        walker.walk(&aplistener, data);

        appls = aplistener.getApplications();
        // Temporary
        for (auto& appl : ugly::get_modulo_appls(filename))
            for (auto& apv : appl.second)
                appls[appl.first].push_back(apv);

        /* Conclude */
        valid = !errl.hasDetectedErrors();
    } else {
        valid = false;
    }
    extracted = true;
}

why3cpp::whyantlr::Extractor::Extractor(const std::string& filename)
    : filename(filename), valid(true), extracted(false) {}

why3cpp::whyantlr::Extractor::~Extractor() {}

why3cpp::ExtractorParser::ExtractorParser(const std::string& filename)
    : WhyMLPGeneric(filename), parser(new whyantlr::Extractor(filename)) {}

why3cpp::ExtractorParser::~ExtractorParser() {}

bool why3cpp::ExtractorParser::hasFailed() const {
    return !parser->isValid();
}

const map<string, string>& why3cpp::ExtractorParser::getVars() const {
    if (!parser->hasExtract())
        parser->extract();
    return parser->getVars();
}

const std::map<std::string, std::string>& why3cpp::ExtractorParser::getLits() const {
    if (!parser->hasExtract())
        parser->extract();
    return parser->getLits();
}

const set<string>& why3cpp::ExtractorParser::getRefs() const {
    if (!parser->hasExtract())
        parser->extract();
    return parser->getRefs();
}

const map<string, list<vector<string>>>& why3cpp::ExtractorParser::getAppls() const {
    if (!parser->hasExtract())
        parser->extract();
    return parser->getAppls();
}
