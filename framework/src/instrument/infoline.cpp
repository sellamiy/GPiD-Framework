#define GPID_FRAMEWORK__INSTRUMENT__INFOLINE_CPP

#include <snlog/snlog.hpp>
#include <gpid/instrument/infoline.hpp>
#include <gpid/utils/stdutils.hpp>

using namespace gpid;
using namespace infoline;

using wtch_t_counters = std::map<std::string, int64_t>;
using wtch_t_data = std::map<std::string, std::string>;
using wtch_t_stack_data = std::map<std::string, std::stack<std::string>>;

struct str_id {
    inline std::string operator()(std::string& v) const { return v; }
};

struct int_str {
    inline std::string operator()(int64_t v) const { return std::to_string(v); }
};

struct stack_first_str {
    inline std::string operator()(std::stack<std::string>& v) const { return v.top(); }
};

instrument::InfolineInstrument::InfolineInstrument() {
    /* For now, does nothing */
}

void instrument::InfolineInstrument::update_count(const std::string& key, int32_t udter)
{
    if (gmisc::ninmap(counter_watchers, key)) {
        std::shared_ptr<int64_t> nptr = std::shared_ptr<int64_t>(new int64_t(0));
        InfoDataPtr idp =
            InfoDataPtr(new PointerInfoData<int64_t, int_str>(key, nptr));
        infoliner.addInfoData(idp);
        counter_watchers[key] = nptr;
    }
    *counter_watchers[key] += udter;
}

void instrument::InfolineInstrument::new_data(const std::string& key, const std::string& value)
{
    if (gmisc::ninmap(data_watchers, key)) {
        std::shared_ptr<std::string> nptr = std::shared_ptr<std::string>(new std::string(value));
        InfoDataPtr idp =
            InfoDataPtr(new PointerInfoData<std::string, str_id>(key, nptr));
        infoliner.addInfoData(idp);
        data_watchers[key] = nptr;
    } else {
        *data_watchers[key] = value;
    }
}
