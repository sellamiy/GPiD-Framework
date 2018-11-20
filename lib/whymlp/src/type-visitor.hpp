#ifndef LIB_WHYMLP__LOCAL_INCLUDE__TYPE_VISTOR_HPP
#define LIB_WHYMLP__LOCAL_INCLUDE__TYPE_VISTOR_HPP

#include <WhyMLBaseVisitor.h>

#define INT_TYPESTR "int"
#define REAL_TYPESTR "real"
#define BOOL_TYPESTR "bool"

/*
inline bool locf_501_isInt(const string& value) {
    snlog::l_fatal() << value << snlog::l_end;
    for (char c : value) if (!std::isdigit(c)) return false;
    return true;
}
*/

class TypeVisitor : public WhyMLBaseVisitor {
    map<string, string>& vars;

    antlrcpp::Any typeDeclaration(antlrcpp::Any source) {
        if (source.isNull()) return source;

        std::string value = source.as<string>();
        if (value.find("typeof:") == 0)
            value = value.substr(7);

        return value;
    }

    antlrcpp::Any typeDeduction(antlrcpp::Any source) {
        if (source.isNull()) return source;

        std::string value = source.as<string>();
        if (value.find("typeof:") == 0)
            value = value.substr(7);

        /* Type of a variable */
        if (vars.count(value) > 0)
            return vars.at(value);

        /* Standard types */
        if (value == INT_TYPESTR || value == REAL_TYPESTR || value == BOOL_TYPESTR)
            return value;

        return string("type-deduction-failed");
    }

    antlrcpp::Any typeApplicationDeduction(const std::string& appname, antlrcpp::Any source) {
        antlrcpp::Any sany = typeDeduction(source);
        if (appname == "ref") {
            const std::string svalue = sany.as<string>();
            return string(svalue + ":ref");
        }
        return sany;
    }
public:
    TypeVisitor(map<string, string>& vars) : vars(vars) {}

    virtual antlrcpp::Any visitLident(WhyMLParser::LidentContext *ctx) override {
        if (ctx->LIDENT() != nullptr) {
            const string& lident = ctx->LIDENT()->getText();
            return string("typeof:" + lident);
        } else {
            return string("internal-error:nullptr");
        }
    }

    virtual antlrcpp::Any visitType(WhyMLParser::TypeContext *ctx) override {
        return typeDeclaration(visitChildren(ctx));
    }

    virtual antlrcpp::Any visitExpr(WhyMLParser::ExprContext *ctx) override {
        if (ctx->ww_application() != nullptr) {
            const std::string& appname = ctx->expr(0)->getText();
            // TODO: The following only deduces type for 1 var applicative types
            // TODO: Should be improved
            return typeApplicationDeduction(appname, visit(ctx->expr(1)));
        }
        return typeDeduction(visitChildren(ctx));
    }

    virtual antlrcpp::Any visitExpr_r_parentheses(WhyMLParser::Expr_r_parenthesesContext *ctx) override {
        return visit(ctx->expr());
    }

    virtual antlrcpp::Any visitInteger(WhyMLParser::IntegerContext*) override {
        return string(INT_TYPESTR);
    }

    virtual antlrcpp::Any visitReal(WhyMLParser::RealContext*) override {
        return string(REAL_TYPESTR);
    }

    virtual antlrcpp::Any visitBoolean(WhyMLParser::BooleanContext*) override {
        return string(BOOL_TYPESTR);
    }
};

/* Type utils functions */

static inline bool isRefType(const std::string& tdata) {
    return tdata.find(":ref") != std::string::npos;
}

static inline const std::string asNonRefType(const std::string& tdata) {
    size_t rpos = tdata.find(":ref");
    return tdata.substr(0, rpos);
}

#endif
