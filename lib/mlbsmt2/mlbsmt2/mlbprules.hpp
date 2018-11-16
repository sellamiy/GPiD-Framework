#ifndef MAGIC_LITERAL_BUILDER_f_SMTLIB2__PRODUCTION_RULES_HPP
#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__PRODUCTION_RULES_HPP

#include <mlbsmt2/mlbInterface.hpp>

namespace mlbsmt2 {

    extern const MagicProductionRulePtr produceDeclaredConsts;
    extern const MagicProductionRulePtr produceBooleanConsts;
    extern const MagicProductionRulePtr produceDeclaredFuns;

    extern const MagicProductionRulePtr produceDeclaredAF_D1;

    extern const MagicProductionRulePtr produceDeclaredEqualities;

    extern const std::map<std::string, MagicProductionRulePtr> productionTable;
    extern const std::map<std::string, std::string> productionDescriptions;

    extern const MagicProductionRulePtr
    produceFromScript(const std::string filename, MagicLiteralData& data);

    extern const MagicProductionRulePtr
    produceFromWhyML(const std::string filename, MagicLiteralData& data);

}

#endif
