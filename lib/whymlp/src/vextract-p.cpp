#define LIB_WHYMLP__V_EXTRACTOR_CPP

#include <antlr4-runtime.h>
#include <snlog/snlog.hpp>
#include <WhyMLLexer.h>
#include <WhyMLParser.h>
#include <WhyMLBaseListener.h>
#include <whymlp/vextract-p.hpp>

using namespace std;

#include "error-listener.hpp"
#include "type-visitor.hpp"

class VextractWhyMLListener : public WhyMLBaseListener {
    map<string, string> vars;
    TypeVisitor typeVisitor;

    inline const std::string getType(antlr4::ParserRuleContext* ctx) {
        try {
            auto result = typeVisitor.visit(ctx);
            if (result.isNotNull())
                return typeVisitor.visit(ctx).as<string>();
            else
                return "unknown";
        } catch (std::bad_cast& e) {
            snlog::l_warn() << "Type deduction failure (token: "
                            << ctx->getText() << ")" << snlog::l_end;
            return "unknown";
        }
    }

public:
    VextractWhyMLListener() : typeVisitor(vars) {}

    inline const map<string, string>& getVars() const { return vars; }

    virtual void exitBound_var(WhyMLParser::Bound_varContext* ctx) override {
        // Bound variables are variables
        auto data = ctx->lident();
        if (data != nullptr) {
            vars[data->getText()] = "untyped";
        }
    }

    virtual void exitParam(WhyMLParser::ParamContext* ctx) override {
        // Param typing
        auto tdata = ctx->type();
        if (tdata != nullptr) {
            const string tvalue = getType(tdata);
            for (auto binder : ctx->binder()) {
                vars[binder->getText()] = tvalue;
            }
        }
    }

    virtual void exitExpr_r_forloop(WhyMLParser::Expr_r_forloopContext* ctx) override {
        auto data = ctx->lident();
        if (data == nullptr)
            snlog::l_internal() << "Unexpected nullptr extracting forloop counter" << snlog::l_end;
        vars[data->getText()] = getType(ctx->expr(0));
    }

    virtual void exitExpr_r_letpattern(WhyMLParser::Expr_r_letpatternContext* ctx) override {
        auto patternNode = ctx->pattern();
        auto typeNode = ctx->expr(0);
        if (patternNode == nullptr || typeNode == nullptr)
            snlog::l_internal() << "Unexpected nullptr extracting let pattern" << snlog::l_end;
        vars[patternNode->getText()] = getType(typeNode);
    }
};

namespace whymlp {
    namespace whyantlr {

        class Vextractor {
            const std::string filename;
            map<string, string> vars;
            set<string> refs;
            bool valid;
        public:
            Vextractor(const std::string& filename);
            ~Vextractor();

            inline constexpr bool isValid() const { return valid; }
            inline bool hasExtract() const { return vars.size() > 0; }

            void extractVars();

            inline const map<string, string>& getVars() const { return vars; }
            inline const set<string>& getRefs() const { return refs; }
        };

    }
}

void whymlp::whyantlr::Vextractor::extractVars() {
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
        VextractWhyMLListener listener;
        walker.walk(&listener, data);

        vars = listener.getVars();

        for (const pair<string, string>& var : vars)
            if (isRefType(var.second))
                refs.insert(var.first);

        for (const std::string& var : refs)
            vars[var] = asNonRefType(vars[var]);

        valid = !errl.hasDetectedErrors();
    } else {
        valid = false;
    }
}

whymlp::whyantlr::Vextractor::Vextractor(const std::string& filename)
    : filename(filename), valid(true) {}

whymlp::whyantlr::Vextractor::~Vextractor() {}

whymlp::VextractParser::VextractParser(const std::string& filename)
    : WhyMLPGeneric(filename), parser(new whyantlr::Vextractor(filename)) {}

whymlp::VextractParser::~VextractParser() {}

bool whymlp::VextractParser::hasFailed() const {
    return !parser->isValid();
}

const map<string, string>& whymlp::VextractParser::getVars() const {
    if (!parser->hasExtract())
        parser->extractVars();
    return parser->getVars();
}

const set<string>& whymlp::VextractParser::getRefs() const {
    if (!parser->hasExtract())
        parser->extractVars();
    return parser->getRefs();
}
