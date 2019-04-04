#define LIB_WHY3CPP__CONVERT_MAP_CPP

#include <snlog/snlog.hpp>
#include <why3cpp/why3utils.hpp>

using namespace why3cpp;

static const stdutils::pair_storage<std::string, std::string> WCM_0110
(
 {}
);

static inline void
update_cm_loc(stdutils::pair_storage<std::string, std::string>& tgt,
              const stdutils::pair_storage<std::string, std::string>& src) {
    for (const auto& p : src)
        tgt.insert(p.first, p.second);
}

Why3ConvertMap::Why3ConvertMap(const std::string& optstr) {
    if (optstr == "auto") {
        update_cm_loc(smap_table, WCM_0110);
    } else {
        snlog::l_error() << "Unknown Why3 Convert-Map initialization option: "
                         << optstr << snlog::l_end;
    }
}
