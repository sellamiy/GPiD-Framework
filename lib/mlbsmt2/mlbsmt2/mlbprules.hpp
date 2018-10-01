#ifndef MAGIC_LITERAL_BUILDER_f_SMTLIB2__PRODUCTION_RULES_HPP
#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__PRODUCTION_RULES_HPP

#include <mlbsmt2/mlbInterface.hpp>

namespace mlbsmt2 {

    extern const MagicProductionRulePtr produceDeclaredConsts;
    extern const MagicProductionRulePtr produceDeclaredFuns;

    extern const std::map<std::string, MagicProductionRulePtr> productionTable;
    extern const std::map<std::string, std::string> productionDescriptions;

}

#endif
