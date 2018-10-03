#ifndef LIB_MAGIC_LITERAL_BUILDER_f_SMTLIB2_CONFIG_HEADER
#define LIB_MAGIC_LITERAL_BUILDER_f_SMTLIB2_CONFIG_HEADER

#include <map>
#include <list>
#include <string>
#include <vector>
#include <memory>
#include <unordered_set>

namespace mlbsmt2 {

    using strptr = std::shared_ptr<std::string>;
    using string_set = std::unordered_set<std::string>;
    using string_list = std::list<std::string>;

    using type_to_name_storage = std::map<std::string, string_set>;
    using name_storage = std::map<std::string, std::string>;
    using function_abst_type = std::pair<string_list, std::string>;
    using function_storage = std::map<std::string, function_abst_type>;

}

#endif
