#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__PRODUCTION_RULES_CPP

#include <unordered_set>
#include <sstream>
#include <snlog/snlog.hpp>
#include <mlbsmt2/mlbconfig.hpp>
#include <mlbsmt2/mlbprules.hpp>

namespace mlbsmt2 {

    class DeclaredConstsProductionRule : public MagicProductionRule {
        ProductionData last = ProductionData();
        name_storage::const_iterator iter;
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
        function_storage::const_iterator iter;
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

    class DeclaredAppliedFunsProductionRule : public DeclaredConstsProductionRule {
    public:
        DeclaredAppliedFunsProductionRule(size_t depth):
            DeclaredConstsProductionRule() {
            if (depth > 0) {
                requires(DataExploitation::ExtractFuns);
            }
            for (size_t c = 0; c < depth; c++) {
                requires(DataExploitation::ApplyFuns);
            }
        }
    };

    class DeclaredEqualitiesProductionRule : public DeclaredConstsProductionRule {
    public:
        DeclaredEqualitiesProductionRule():
            DeclaredConstsProductionRule() {
            requires(DataExploitation::ApplyEquality);
        }
    };

}

using namespace mlbsmt2;

extern const MagicProductionRulePtr mlbsmt2::produceDeclaredConsts =
    MagicProductionRulePtr(new DeclaredConstsProductionRule());

extern const MagicProductionRulePtr mlbsmt2::produceDeclaredFuns =
    MagicProductionRulePtr(new DeclaredFunsProductionRule());

extern const MagicProductionRulePtr mlbsmt2::produceDeclaredAF_D1 =
    MagicProductionRulePtr(new DeclaredAppliedFunsProductionRule(1));

extern const MagicProductionRulePtr mlbsmt2::produceDeclaredEqualities =
    MagicProductionRulePtr(new DeclaredEqualitiesProductionRule());

extern const std::map<std::string, MagicProductionRulePtr> mlbsmt2::productionTable =
    {
        { "declared-consts", produceDeclaredConsts },
        { "declared-funs", produceDeclaredFuns },
        { "applied-funs", produceDeclaredAF_D1 },
        { "applied-equality", produceDeclaredEqualities }
    };

extern const std::map<std::string, std::string> mlbsmt2::productionDescriptions =
    {
        { "declared-consts", "All declared constants" },
        { "declared-funs", "All declared functions w/ generic pvars" },
        { "applied-funs", "All declared constants and functions applied up to depth 1" },
        { "applied-equality", "Equalities on all declared constants" }
    };
