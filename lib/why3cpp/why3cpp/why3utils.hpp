#ifndef LIB_WHY3CPP__PLATFORM_GENERAL_UTILS_HEADER
#define LIB_WHY3CPP__PLATFORM_GENERAL_UTILS_HEADER

#include <snlog/snlog.hpp>
#include <stdutils/pairstorage.hpp>
#include <lisptp/lisptp.hpp>

namespace why3cpp {

    using transfermap_t = std::map<std::string, std::vector<std::string>>;

    class Why3ConvertMap {
        std::set<std::string> refs;
        /* Forward conversion: smtlib2 (obtained from whyml) -> whyml */
        /* Backward conversion: whyml -> smtlib2 || unsanitized smtlib2 -> smtlib2 */
        stdutils::pair_storage<std::string, std::string> smap_table;

        transfermap_t transfermap;
        std::map<std::pair<std::string, size_t>, std::string> transfer_cache;

        size_t localid;
    public:
        Why3ConvertMap() {}
        Why3ConvertMap(const std::string& optstr);
        Why3ConvertMap(const std::set<std::string>& refs) : refs(refs) {}
        Why3ConvertMap(const stdutils::pair_storage<std::string, std::string>& smap_table)
            : smap_table(smap_table) {}
        Why3ConvertMap(const std::set<std::string>& refs,
                       const stdutils::pair_storage<std::string, std::string>& smap_table)
            : refs(refs), smap_table(smap_table) {}
        Why3ConvertMap(const stdutils::pair_storage<std::string, std::string>& smap_table,
                       const std::set<std::string>& refs)
            : refs(refs), smap_table(smap_table) {}
        Why3ConvertMap(const Why3ConvertMap& o) : refs(o.refs), smap_table(o.smap_table) {}

        inline void addRefs(const std::set<std::string>& _refs) {
            for (auto& r : _refs) refs.insert(r);
        }

        inline bool isref(const std::string& t) const { return refs.count(t) > 0; }

        inline void setLocalId(const size_t& s) { localid = s; }
        inline constexpr size_t getLocalId() const { return localid; }

        inline bool emptySymbolMap() const { return smap_table.empty(); }

        inline void addSymbolMapping(const std::string& fwd, const std::string bck) {
            smap_table.insert(fwd, bck);
        }

        inline bool hasForwardMapping(const std::string& s) const {
            return smap_table.contains(s);
        }
        inline bool hasBackwardMapping(const std::string& s) const {
            return smap_table.rcontains(s);
        }

        inline const std::string& forwardMapping(const std::string& s) const {
            return smap_table.at(s);
        }
        inline const std::string& backwardMapping(const std::string& s) const {
            return smap_table.rat(s);
        }

        inline void changeTransferMap(const transfermap_t& tm) {
            transfermap = tm;
        }

        inline const std::string& transfer(const std::string& s) {
            if (stdutils::inmap(transfermap, s)) {
                const std::string& res = transfermap.at(s).back();
                const auto cdata = std::pair<std::string, size_t>(res, localid);
                transfer_cache[cdata] = s;
                return res;
            } else {
                return s;
            }
        }

        inline const std::string& backTransfer(const std::string& s) const {
            const auto cdata = std::pair<std::string, size_t>(s, localid);
            if (stdutils::inmap(transfer_cache, cdata)) {
                return transfer_cache.at(cdata);
            } else {
                return s;
            }
        }
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

    class BackwardSmtl2CV : public lisptp::LispTreeVisitor<std::string> {
        const Why3ConvertMap& cmap;
    protected:
        inline virtual std::string handle_term(const std::string& t) const override {
            return t;
        }

        virtual std::string handle_call(const std::string& op, const std::vector<std::string>& lvs)
            const override;
    public:
        BackwardSmtl2CV(const Why3ConvertMap& cmap) : cmap(cmap) {}

        inline std::string convert(const std::string& smtl2data) const {
            return visit(lisptp::parse(smtl2data));
        }
    };

    static inline std::string SmtBackwardConvert(const std::string& smtl2data, const Why3ConvertMap& cmap) {
        if (cmap.emptySymbolMap()) {
            return smtl2data;
        }
        BackwardSmtl2CV converter(cmap);
        return converter.convert(smtl2data);
    }

}

#endif
