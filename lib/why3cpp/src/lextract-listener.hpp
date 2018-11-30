#ifndef LIB_WHY3CPP__LOCAL_INCLUDE__L_EXTRACT_LISTENER_HPP
#define LIB_WHY3CPP__LOCAL_INCLUDE__L_EXTRACT_LISTENER_HPP

#include <WhyMLBaseListener.h>

#include "type-visitor.hpp"

class LextractWhyMLListener : public WhyMLBaseListener {
    map<string, string> literals;
    stack<pair<string, string>> lstack;
public:
    LextractWhyMLListener() {}

    inline const map<string, string>& getLiterals() {
        unstack();
        return literals;
    }

    inline void unstack() {
        while (!lstack.empty()) {
            literals.insert(lstack.top());
            lstack.pop();
        }
    }

    virtual void exitInteger(WhyMLParser::IntegerContext* ctx) override {
        lstack.push(pair<string, string>(ctx->INTEGER()->getText(), INT_TYPESTR));
    }

    virtual void exitReal(WhyMLParser::RealContext* ctx) override {
        lstack.push(pair<string, string>(ctx->REAL()->getText(), REAL_TYPESTR));
    }

    virtual void exitExpr(WhyMLParser::ExprContext* ctx) override {
        if (!lstack.empty() && ctx->op() != nullptr && ctx->expr().size() == 1) {
            // Prefix operator extraction
            lstack.top().first = ctx->op()->getText() + lstack.top().first;
            lstack.top().second = prefixTypeConversion(ctx->op()->getText(), lstack.top().second);
        } else {
            unstack();
        }
    }
};

#endif
