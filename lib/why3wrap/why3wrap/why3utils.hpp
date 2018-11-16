#ifndef LIB_WHY3WRAP__PLATFORM_GENERAL_UTILS_HEADER
#define LIB_WHY3WRAP__PLATFORM_GENERAL_UTILS_HEADER

#include <lisptp/lisptp.hpp>

namespace why3wrap {

    class Why3Smtl2CV : public lisptp::LispTreeVisitor<std::string> {
    protected:
        inline virtual std::string handle_term(const std::string& t) const override
        { return "!" + t; } // TODO: UNSAFE!!!!!

        virtual std::string handle_call(const std::string& op, const std::list<std::string>& lvs)
            const override;
    public:
        inline std::string convert(const std::string& smtl2data) const {
            return visit(lisptp::parse(smtl2data));
        }
    };

    const Why3Smtl2CV Smt2Why3Converter;

    static inline std::string Smt2Why3(const std::string& smtl2data) {
        return Smt2Why3Converter.convert(smtl2data);
    }

}

#endif
