#ifndef LIB_WHY3CPP__LOCAL_INCLUDE__APL_EXTRACT_LISTENER_HPP
#define LIB_WHY3CPP__LOCAL_INCLUDE__APL_EXTRACT_LISTENER_HPP

#include <WhyMLBaseListener.h>

class AplextractWhyMLListener : public WhyMLBaseListener {
    map<string, list<vector<string>>> applications;

    void extractApplication(WhyMLParser::Priority_expr_applContext *ctx) {
        const std::string& appname = ctx->priority_expr_tight(0)->getText();
        if (appname == "mod") {
            const std::string refname = appname + ctx->priority_expr_tight(2)->getText();
            applications[refname].push_back({ ctx->priority_expr_tight(1)->getText() });
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
};

#endif
