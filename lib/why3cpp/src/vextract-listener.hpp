#ifndef LIB_WHY3CPP__LOCAL_INCLUDE__V_EXTRACT_LISTENER_HPP
#define LIB_WHY3CPP__LOCAL_INCLUDE__V_EXTRACT_LISTENER_HPP

#include <WhyMLBaseListener.h>

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
        auto typeNode = ctx->priority_expr_if();
        if (patternNode == nullptr || typeNode == nullptr)
            snlog::l_internal() << "Unexpected nullptr extracting let pattern" << snlog::l_end;
        vars[patternNode->getText()] = getType(typeNode);
    }
};

#endif
