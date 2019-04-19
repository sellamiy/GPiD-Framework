#define LIB_WHY3CPP__VC_INJECTIONS_CPP

#include <map>
#include <vector>
#include <snlog/snlog.hpp>
#include <stdutils/collections.hpp>
#include <why3cpp/why3vcinject.hpp>

using namespace why3cpp;

using injection_table_t = std::map<std::string, std::set<std::string>>;
using injection_data_table_t = std::map<std::string, std::string>;
using injection_table_set = std::vector<injection_table_t>;

// TODO: Add raw injection data here

static const injection_table_set WHY3_INJECTION_TABLES_SCORE
({

 });

static const injection_data_table_t WHY3_SMTL2_INJECTION_DATA
({

 });

extern bool why3cpp::vcinjectable
(const std::string& source_decl, const std::set<std::string>& decls) {
    for (const injection_table_t& table : WHY3_INJECTION_TABLES_SCORE)
        if (stdutils::inmap(table, source_decl))
            for (const std::string& pmissing : table.at(source_decl))
                if (stdutils::ninset(decls, pmissing))
                    return true;
    return false;
}

extern void why3cpp::vcinject
(std::stringstream& ss, const std::string& source_decl, const std::set<std::string>& decls) {
    for (const injection_table_t& table : WHY3_INJECTION_TABLES_SCORE)
        if (stdutils::inmap(table, source_decl))
            for (const std::string& pmissing : table.at(source_decl))
                if (stdutils::ninset(decls, pmissing))
                    ss << WHY3_SMTL2_INJECTION_DATA.at(pmissing) << '\n';
}
