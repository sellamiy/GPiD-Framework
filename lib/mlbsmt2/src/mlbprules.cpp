#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__PRODUCTION_RULES_CPP

#include <unordered_set>
#include <sstream>
#include <snlog/snlog.hpp>
#include <mlbsmt2/mlbconfig.hpp>
#include <mlbsmt2/mlbprules.hpp>

namespace mlbsmt2 {

    class DeclaredConstsProductionRule : public MagicProductionRule {
        ProductionData last = ProductionData();
        std::map<std::string, std::string>::const_iterator iter;
        bool iter_inited = false;

        void ensure_iter_inited(const MagicLiteralData& data) {
            if (!iter_inited) {
                iter = data.consts_iterator();
                iter_inited = true;
            }
        }
    public:
        DeclaredConstsProductionRule() {
            requires(DataExploitation::ExtractConsts);
        }
        virtual bool hasNext(const MagicLiteralData& data) override {
            ensure_iter_inited(data);
            return iter != data.consts_iterator_end();
        }
        virtual ProductionData& next(const MagicLiteralData& data) override {
            ensure_iter_inited(data);
            last = ProductionData(iter++->first);
            return last;
        }
    };

    class DeclaredFunsProductionRule : public MagicProductionRule {
        ProductionData last = ProductionData();
        std::map<std::string, std::pair<string_list, std::string>>::const_iterator iter;
        bool iter_inited = false;

        void ensure_iter_inited(const MagicLiteralData& data) {
            if (!iter_inited) {
                iter = data.funs_iterator();
                iter_inited = true;
            }
        }
    public:
        DeclaredFunsProductionRule() {
            requires(DataExploitation::ExtractFuns);
        }
        virtual bool hasNext(const MagicLiteralData& data) override {
            ensure_iter_inited(data);
            return iter != data.funs_iterator_end();
        }
        virtual ProductionData& next(const MagicLiteralData& data) override {
            ensure_iter_inited(data);
            std::stringstream ss;
            ss << "(" << iter->first;
            for (const std::string paramt : iter->second.first) {
                ss << " " << "_v$" << paramt;
            }
            ss << ")";
            ++iter;
            last = ProductionData(ss.str());
            return last;
        }
    };

}

using namespace mlbsmt2;

extern const MagicProductionRulePtr mlbsmt2::produceDeclaredConsts =
    MagicProductionRulePtr(new DeclaredConstsProductionRule());

extern const MagicProductionRulePtr mlbsmt2::produceDeclaredFuns =
    MagicProductionRulePtr(new DeclaredFunsProductionRule());
