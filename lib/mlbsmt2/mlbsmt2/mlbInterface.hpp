#ifndef MAGIC_LITERAL_BUILDER_f_SMTLIB2__INTERFACE_HPP
#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__INTERFACE_HPP

#include <map>
#include <list>
#include <string>
#include <memory>
#include <unordered_set>
#include <smtlib2utils/smtlib2utils.hpp>
#include <mlbsmt2/mlberrors.hpp>

namespace mlbsmt2 {

    using strptr = std::shared_ptr<std::string>;
    using string_set = std::unordered_set<std::string>;
    using string_list = std::list<std::string>;

    enum class DataExploitation {
        ExtractConsts, ExtractFuns, ApplyFuns, ApplyEquality
    };

    class MagicLiteralData;

    class MagicProductionRule {
        std::list<DataExploitation> requirements;
    public:

        struct ProductionData {
            std::string value;
            bool valid;
            ProductionData() : value(""), valid(false) {}
            ProductionData(const std::string value, bool valid=true)
                : value(value), valid(valid) {}
            ProductionData(const ProductionData& o)
                : value(o.value), valid(o.valid) {}
            ProductionData& operator= (const ProductionData& o) {
                value = o.value;
                valid = o.valid;
                return *this;
            }
        };

        MagicProductionRule& requires(DataExploitation e);
        inline const std::list<DataExploitation>& getRequirements() const
        { return requirements; }

        virtual bool hasNext(const MagicLiteralData& data) = 0;
        virtual ProductionData& next(const MagicLiteralData& data) = 0;
    };

    using MagicProductionRulePtr = std::shared_ptr<MagicProductionRule>;

    class MagicParsingHandler;

    class MagicLiteralData {
        std::unique_ptr<MagicParsingHandler> handler;
        smtlib2utils::SMTl2StringMemory smem;

        std::map<std::string, string_set> consts_type_in;
        std::map<std::string, std::string> consts_name_in;

        std::map<std::string, string_set> funs_type_in;
        std::map<std::string, std::pair<string_list, std::string>> funs_name_in;

        void updateConsts(const std::map<std::string, std::string>& toAdd);

        void storeConst(const std::string name, const std::string type);
        void storeFun(const std::string name, const string_list& params, const std::string rtype);

        void addFunToConsts(std::map<std::string, std::string>& newConsts,
                            const std::string& funname,
                            const std::pair<string_list, std::string>& fun);
        void addSymetricFunToConsts
        (std::map<std::string, std::string>& newConsts,
         const std::string& funname, const std::string& ptype, const std::string& rtype);
    public:
        inline typename std::map<std::string, std::string>::const_iterator consts_iterator() const
        { return consts_name_in.begin(); }
        inline typename std::map<std::string, std::string>::const_iterator consts_iterator_end() const
        { return consts_name_in.end(); }
        inline typename std::map<std::string, std::pair<string_list, std::string>>
        ::const_iterator funs_iterator() const
        { return funs_name_in.begin(); }
        inline typename std::map<std::string, std::pair<string_list, std::string>>
        ::const_iterator funs_iterator_end() const
        { return funs_name_in.end(); }
    public:
        MagicLiteralData();
        ~MagicLiteralData();

        inline MagicParsingHandler& getHandler() { return *handler; }
        inline smtlib2utils::SMTl2StringMemory& getMemory() { return smem; }

        void extractConsts();
        void extractFuns();
        void applyFuns();
        void applyEquality();
    };

    class MagicLiteralBuilder {
        enum class BuilderState { Initialized, Exploited, Building, Complete, Error };
        BuilderState state = BuilderState::Initialized;

        std::list<MagicProductionRulePtr> rules;
        std::map<DataExploitation, bool> exploitations;

        MagicLiteralData data;

        bool exploitData(DataExploitation e);
    public:
        MagicLiteralBuilder& uses(const MagicProductionRulePtr& rule);

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

    inline MagicLiteralBuilder& MagicLiteralBuilder::uses(const MagicProductionRulePtr& rule) {
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
        while(!rules.empty() && !rules.front()->hasNext(data)) {
            // Remove already completed rule
            rules.pop_front();
        }
        state = rules.empty() ? BuilderState::Complete : BuilderState::Exploited;
    }

    inline std::string MagicLiteralBuilder::buildLiteral() {
        if (!buildable())
            throw BuilderStatusError("Illegal builder state for literal build");
        if (state == BuilderState::Exploited)
            state = BuilderState::Building;
        typename MagicProductionRule::ProductionData& pdata = rules.front()->next(data);
        while(!rules.empty() && !rules.front()->hasNext(data))
            // Remove already completed rule
            rules.pop_front();
        if (rules.empty())
            state = BuilderState::Complete;
        if (!pdata.valid)
            state = BuilderState::Error;
        return pdata.value;
    }

}

#endif
