#ifndef LIB_WHY3CPP__PLATFORM_GENERAL_UTILS_HEADER
#define LIB_WHY3CPP__PLATFORM_GENERAL_UTILS_HEADER

#include <set>
#include <lisptp/lisptp.hpp>

namespace why3cpp {

    class Why3Smtl2CV : public lisptp::LispTreeVisitor<std::string> {
        const std::set<std::string>& refs;
    protected:
        inline virtual std::string handle_term(const std::string& t) const override {
            return (refs.count(t) > 0 ? "!" : "") + t;
        }

        virtual std::string handle_call(const std::string& op, const std::vector<std::string>& lvs)
            const override;
    public:
        Why3Smtl2CV(const std::set<std::string>& refs) : refs(refs) {}

        inline std::string convert(const std::string& smtl2data) const {
            return visit(lisptp::parse(smtl2data));
        }
    };

    static inline std::string Smt2Why3(const std::string& smtl2data, const std::set<std::string>& refs) {
        Why3Smtl2CV Smt2Why3Converter(refs);
        return Smt2Why3Converter.convert(smtl2data);
    }

}

#endif
