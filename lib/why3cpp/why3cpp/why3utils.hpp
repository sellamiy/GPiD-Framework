#ifndef LIB_WHY3CPP__PLATFORM_GENERAL_UTILS_HEADER
#define LIB_WHY3CPP__PLATFORM_GENERAL_UTILS_HEADER

#include <set>
#include <lisptp/lisptp.hpp>

namespace why3cpp {

    class Why3ConvertMap {
        std::set<std::string> refs;
    public:
        Why3ConvertMap() {}
        Why3ConvertMap(const std::set<std::string>& refs) : refs(refs) {}
        Why3ConvertMap(const Why3ConvertMap& o) : refs(o.refs) {}

        inline void addRefs(const std::set<std::string>& _refs) {
            for (auto& r : _refs) refs.insert(r);
        }

        inline bool isref(const std::string& t) const { return refs.count(t) > 0; }
    };

    class Why3Smtl2CV : public lisptp::LispTreeVisitor<std::string> {
        const Why3ConvertMap& cmap;
    protected:
        inline virtual std::string handle_term(const std::string& t) const override {
            return (cmap.isref(t) ? "!" : "") + t;
        }

        virtual std::string handle_call(const std::string& op, const std::vector<std::string>& lvs)
            const override;
    public:
        Why3Smtl2CV(const Why3ConvertMap& cmap) : cmap(cmap) {}

        inline std::string convert(const std::string& smtl2data) const {
            return visit(lisptp::parse(smtl2data));
        }
    };

    static inline std::string Smt2Why3(const std::string& smtl2data, const Why3ConvertMap& cmap) {
        Why3Smtl2CV Smt2Why3Converter(cmap);
        return Smt2Why3Converter.convert(smtl2data);
    }

}

#endif
