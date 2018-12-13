#ifndef LIB_WHY3CPP__LOCAL_INCLUDE__APL_EXTRACT_LISTENER_HPP
#define LIB_WHY3CPP__LOCAL_INCLUDE__APL_EXTRACT_LISTENER_HPP

#include <WhyMLBaseListener.h>

static inline const std::string deref(const std::string& source) {
    size_t rloc = source.find("!");
    return rloc == std::string::npos ? source : source.substr(rloc+1);
}

class AplextractWhyMLListener : public WhyMLBaseListener {
    map<string, list<vector<string>>> applications;

    void extractApplication(WhyMLParser::Priority_expr_applContext *ctx) {
        const std::string& appname = ctx->priority_expr_tight(0)->getText();
        if (appname == "mod") {
            const std::string refname = appname + ctx->priority_expr_tight(2)->getText();
            applications[refname].push_back({ deref(ctx->priority_expr_tight(1)->getText()) });
        }
    }

    void extractOperation(WhyMLParser::Priority_expr_plusContext *ctx) {
        const std::string& opname = ctx->infixop2()->getText();
        if (opname == "+") {
            const std::string& left = ctx->priority_expr_mult()->getText();
            const std::string& right = ctx->priority_expr_plus()->getText();
            applications[opname].push_back({ deref(left), deref(right) });
        }
    }

    void extractOperation(WhyMLParser::Priority_expr_multContext *ctx) {
        const std::string& opname = ctx->infixop3()->getText();
        if (opname == "*") {
            const std::string& left = ctx->priority_expr_low()->getText();
            const std::string& right = ctx->priority_expr_mult()->getText();
            applications[opname].push_back({ deref(left), deref(right) });
        }
    }

    void extractOperation(WhyMLParser::Priority_term_plusContext *ctx) {
        const std::string& opname = ctx->infixop2()->getText();
        if (opname == "+") {
            const std::string& left = ctx->priority_term_mult()->getText();
            const std::string& right = ctx->priority_term_plus()->getText();
            applications[opname].push_back({ deref(left), deref(right) });
        }
    }

    void extractOperation(WhyMLParser::Priority_term_multContext *ctx) {
        const std::string& opname = ctx->infixop3()->getText();
        if (opname == "*") {
            const std::string& left = ctx->priority_term_low()->getText();
            const std::string& right = ctx->priority_term_mult()->getText();
            applications[opname].push_back({ deref(left), deref(right) });
        }
    }

public:
    AplextractWhyMLListener() {}

    inline const map<string, list<vector<string>>>& getApplications() const { return applications; }

    virtual void enterPriority_expr_appl(WhyMLParser::Priority_expr_applContext *ctx) override {
        if (ctx->priority_expr_tight().size() > 1) {
            extractApplication(ctx);
        }
        enterEveryRule(ctx);
    }

    virtual void enterPriority_expr_plus(WhyMLParser::Priority_expr_plusContext *ctx) override {
        if (ctx->infixop2() != nullptr) {
            extractOperation(ctx);
        }
        enterEveryRule(ctx);
    }

    virtual void enterPriority_term_plus(WhyMLParser::Priority_term_plusContext *ctx) override {
        if (ctx->infixop2() != nullptr) {
            extractOperation(ctx);
        }
        enterEveryRule(ctx);
    }

    virtual void enterPriority_expr_mult(WhyMLParser::Priority_expr_multContext *ctx) override {
        if (ctx->infixop3() != nullptr) {
            extractOperation(ctx);
        }
        enterEveryRule(ctx);
    }

    virtual void enterPriority_term_mult(WhyMLParser::Priority_term_multContext *ctx) override {
        if (ctx->infixop3() != nullptr) {
            extractOperation(ctx);
        }
        enterEveryRule(ctx);
    }
};

#endif
