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
    { { "length", { "length1" } },
      { "hd", { "hd1" } },
      { "tl", { "tl1" } }
    }
 });

static const injection_data_table_t WHY3_SMTL2_INJECTION_CLASSIC_DATA
({
    { "length1", "" },
    { "hd1", "" },
    { "tl1", "" },
 });

static const injection_data_table_t WHY3_SMTL2_INJECTION_ALTERGO_DATA
({
    { "length1", "(declare-fun length1 (uni) Int) (assert (forall ((a uni)) (= (length1 a) (length int a))))" },
    { "hd1", "(declare-fun hd1 (uni) Int) (assert (forall ((l uni)) (= (hd1 l) ((tb2t (hd int l))))))" },
    { "tl1", "" },
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
(std::stringstream& ss, const VCInjectionMode mode,
 const std::string& source_decl, const std::set<std::string>& decls) {
    for (const injection_table_t& table : WHY3_INJECTION_TABLES_SCORE)
        if (stdutils::inmap(table, source_decl))
            for (const std::string& pmissing : table.at(source_decl))
                if (stdutils::ninset(decls, pmissing)) {
                    if (mode == VCInjectionMode::Classic) {
                        ss << WHY3_SMTL2_INJECTION_CLASSIC_DATA.at(pmissing) << '\n';
                    } else {
                        ss << WHY3_SMTL2_INJECTION_ALTERGO_DATA.at(pmissing) << '\n';
                    }
                }
}
