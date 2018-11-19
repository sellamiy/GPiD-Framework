#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__PRODUCTION_RULES_CPP

#include <unordered_set>
#include <sstream>
#include <snlog/snlog.hpp>
#include <ugly/ugly.hpp>
#include <whymlp/whymlp.hpp>
#include <mlbsmt2/mlbconfig.hpp>
#include <mlbsmt2/mlbprules.hpp>
#include <mlbsmt2/mlbscript.hpp>

namespace mlbsmt2 {

    class DeclaredConstsProductionRule : public MagicProductionRule {
        ProductionData last = ProductionData();
    protected:
        name_storage::const_iterator iter;
        bool iter_inited = false;

        void ensure_iter_inited(const MagicLiteralData& data) {
            if (!iter_inited) {
                iter = data.consts_iterator();
                iter_inited = true;
                hasNext(data); // Forces iterator initialization
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

    class TypedConstsProductionRule : public DeclaredConstsProductionRule {
        std::string target_type;
    public:
        TypedConstsProductionRule(const std::string type)
            : DeclaredConstsProductionRule(), target_type(type) {}

        virtual bool hasNext(const MagicLiteralData& data) override {
            ensure_iter_inited(data);
            while (iter != data.consts_iterator_end() && iter->second != target_type) ++iter;
            return iter != data.consts_iterator_end();
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

    class EncapsulatedProductionRules : public MagicProductionRule {
        ProductionData last = ProductionData();

        using MprList = std::list<MagicProductionRulePtr>;
        MprList subrules;
        MprList::iterator iter;
        bool iter_inited = false;

        void ensure_iter_inited() {
            if (!iter_inited) {
                iter = subrules.begin();
                iter_inited = true;
            }
        }
    public:
        EncapsulatedProductionRules() {}
        EncapsulatedProductionRules(const MprList& ilist, bool forwardReqs=true)
            : subrules(ilist)
        {
            if (forwardReqs)
                for (auto rule : subrules)
                    for (auto req : rule->getRequirements())
                        requires(req);
        }

        inline void addRule(const MagicProductionRulePtr& rule, bool forwardReqs=true) {
            if (iter_inited) throw InternalError("Trying to add rule on iteration");
            subrules.push_back(rule);
            if (forwardReqs)
                for (auto req : rule->getRequirements())
                    requires(req);
        }

        virtual bool hasNext(const MagicLiteralData&) override {
            ensure_iter_inited();
            return iter != subrules.end();
        }
        virtual ProductionData& next(const MagicLiteralData& data) override {
            ensure_iter_inited();
            last = (*iter)->next(data);
            while(iter != subrules.end() && !(*iter)->hasNext(data)) ++iter;
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

extern const MagicProductionRulePtr mlbsmt2::produceBooleanConsts =
    MagicProductionRulePtr(new TypedConstsProductionRule("Bool"));

extern const MagicProductionRulePtr mlbsmt2::produceDeclaredFuns =
    MagicProductionRulePtr(new DeclaredFunsProductionRule());

extern const MagicProductionRulePtr mlbsmt2::produceDeclaredAF_D1 =
    MagicProductionRulePtr(new DeclaredAppliedFunsProductionRule(1));

extern const MagicProductionRulePtr mlbsmt2::produceDeclaredEqualities =
    MagicProductionRulePtr(new DeclaredEqualitiesProductionRule());

extern const std::map<std::string, MagicProductionRulePtr> mlbsmt2::productionTable =
    {
        { "declared-consts", produceDeclaredConsts },
        { "boolean-consts", produceBooleanConsts },
        { "declared-funs", produceDeclaredFuns },
        { "applied-funs", produceDeclaredAF_D1 },
        { "applied-equality", produceDeclaredEqualities }
    };

extern const std::map<std::string, std::string> mlbsmt2::productionDescriptions =
    {
        { "declared-consts", "All declared constants" },
        { "boolean-consts", "All boolean constants" },
        { "declared-funs", "All declared functions w/ generic pvars" },
        { "applied-funs", "All declared constants and functions applied up to depth 1" },
        { "applied-equality", "Equalities on all declared constants" }
    };

extern const MagicProductionRulePtr mlbsmt2::
produceFromScript(const std::string filename, MagicLiteralData& data) {
    MlbScriptParser parser(filename);
    parser.parse();
    const MlbScriptCHandler& datah = parser.getHandler();
    data.updateConsts(datah.getLoadedConsts());
    data.updateFuns(datah.getLoadedFuns());
    /* TODO: This is never explicitly deleted, check that it is dynamically */
    std::shared_ptr<EncapsulatedProductionRules> capsule(new EncapsulatedProductionRules());
    data.updateApps(datah.getApplications());
    capsule->requires(DataExploitation::ApplyScript);
    capsule->addRule(produceBooleanConsts);
    return capsule;
}

extern const MagicProductionRulePtr mlbsmt2::
produceFromWhyML(const std::string filename, MagicLiteralData& data) {
    whymlp::VextractParser parser(filename);
    data.updateConsts(parser.getVars()); // TODO: Perform a type convertion
    snlog::l_warn() << "Type conversion WhyML typenames -> Smtl2 typenames not implemented" << snlog::l_end;

    // TODO: Improve the modularity
    std::list<MlbApplication> applications;

    if (ugly::mapHasValue<std::string, std::string>(parser.getVars(), "int")) {
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "=", { "int" }));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "distinct", { "int" }));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, ">", { "int" }));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, ">=", { "int" }));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "<", { "int" }));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "<=", { "int" }));
    }
    if (ugly::mapHasValue<std::string, std::string>(parser.getVars(), "bool")) {
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "=", { "bool" }));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "distinct", { "bool" }));
    }

    data.updateApps(applications);

    std::shared_ptr<EncapsulatedProductionRules> capsule(new EncapsulatedProductionRules());
    capsule->requires(DataExploitation::ApplyScript);
    capsule->addRule(produceBooleanConsts);
    return capsule;
}

