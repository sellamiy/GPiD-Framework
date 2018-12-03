#ifndef LIB_WHY3CPP__LOCAL_INCLUDE__APL_EXTRACT_LISTENER_HPP
#define LIB_WHY3CPP__LOCAL_INCLUDE__APL_EXTRACT_LISTENER_HPP

#include <WhyMLBaseListener.h>

class AplextractWhyMLListener : public WhyMLBaseListener {
    map<string, list<vector<string>>> applications;

    void extractApplication(WhyMLParser::ExprContext *ctx) {
        const std::string& appname = ctx->expr(0)->getText();
        if (appname == "mod") {
            const std::string refname = appname + ctx->expr(2)->getText();
            applications[refname].push_back({ ctx->expr(1)->getText() });
        }
    }

public:
    AplextractWhyMLListener() {}

    inline const map<string, list<vector<string>>>& getApplications() const { return applications; }

    virtual void enterExpr(WhyMLParser::ExprContext *ctx) override {
        if (ctx->ww_application() != nullptr) {
            extractApplication(ctx);
        }
        enterEveryRule(ctx);
    }
};

#endif
