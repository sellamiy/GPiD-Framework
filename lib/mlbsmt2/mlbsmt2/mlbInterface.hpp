#ifndef MAGIC_LITERAL_BUILDER_f_SMTLIB2__INTERFACE_HPP
#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__INTERFACE_HPP

#include <list>
#include <map>
#include <string>
#include <memory>

#include <mlbsmt2/mlberrors.hpp>

namespace mlbsmt2 {

    enum class DataExploitation {
        ExtractConsts, ExtractFuns
    };

    class MagicProductionRule {
        std::list<DataExploitation> requirements;
    public:

        struct ProductionData {
            const std::string value;
            bool valid;
            ProductionData(const std::string value, bool valid=true)
                : value(value), valid(valid) {}
        };

        MagicProductionRule& requires(DataExploitation e);
        inline const std::list<DataExploitation>& getRequirements() const
        { return requirements; }

        virtual bool hasNext() = 0;
        virtual ProductionData& next() = 0;
    };

    using MagicProductionRulePtr = std::shared_ptr<MagicProductionRule>;

    class MagicLiteralData;

    class MagicLiteralBuilder {
        enum class BuilderState { Initialized, Exploited, Building, Complete, Error };
        BuilderState state;

        std::list<MagicProductionRulePtr> rules;
        std::map<DataExploitation, bool> exploitations;

        std::unique_ptr<MagicLiteralData> data;

        bool exploitData(DataExploitation e);
    public:
        MagicLiteralBuilder();
        ~MagicLiteralBuilder();

        MagicLiteralBuilder& uses(MagicProductionRulePtr& rule);

        void loadSMTlib2File(const std::string filename);

        void exploitData();

        inline bool valid() { return state != BuilderState::Error; }
        inline bool complete() { return state == BuilderState::Complete; }
        inline bool exploitable() { return state == BuilderState::Initialized; }
        inline bool buildable() {
            return state == BuilderState::Exploited
                || state == BuilderState::Building;
        }

        std::string buildLiteral();
    };

    // Implementations

    inline MagicProductionRule& MagicProductionRule::requires(DataExploitation e) {
        requirements.push_back(e);
        return *this;
    }

    inline MagicLiteralBuilder& MagicLiteralBuilder::uses(MagicProductionRulePtr& rule) {
        rules.push_back(rule);
        return *this;
    }

    inline void MagicLiteralBuilder::exploitData() {
        if (!exploitable())
            throw BuilderStatusError("Illegal builder state for data exploitation");
        for (auto rule : rules) {
            for (auto exploitation : rule->getRequirements()) {
                if (!exploitations[exploitation])
                    exploitations[exploitation] = exploitData(exploitation);
                if (!exploitations[exploitation])
                    state = BuilderState::Error;
            }
        }
        state = rules.empty() ? BuilderState::Complete : BuilderState::Exploited;
    }

    inline std::string MagicLiteralBuilder::buildLiteral() {
        if (!buildable())
            throw BuilderStatusError("Illegal builder state for literal build");
        if (state == BuilderState::Exploited)
            state = BuilderState::Building;
        typename MagicProductionRule::ProductionData& data = rules.front()->next();
        if (!rules.front()->hasNext())
            rules.pop_front();
        if (rules.empty())
            state = BuilderState::Complete;
        if (!data.valid)
            state = BuilderState::Error;
        return data.value;
    }

}

#endif
