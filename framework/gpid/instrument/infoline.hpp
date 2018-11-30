/**
 * \file gpid/instrument/infoline.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__INSTRUMENT__INFOLINE_HPP
#define GPID_FRAMEWORK__INSTRUMENT__INFOLINE_HPP

#include <map>
#include <stack>
#include <string>
#include <memory>
#include <stdutils/infoline-bsr.hpp>

namespace gpid {
namespace instrument {

    /**
     * \brief Class for infolining details of the computation.
     * \ingroup gpidinstrumentlib
     */
    class InfolineInstrument {

        stdutils::BsRInfoliner infoliner;

        std::map<std::string, std::shared_ptr<int64_t>> counter_watchers;
        std::map<std::string, std::shared_ptr<std::string>> data_watchers;
        std::map<std::string, std::stack<std::string>> stack_watchers;
        std::map<std::string, std::shared_ptr<std::string>> topstack_watchers;
        
    public:
        InfolineInstrument();

        inline void initialize() { infoliner.setup(); }
        inline void terminate() { infoliner.discard(); }

        void update_count(const std::string& key, int32_t udter);
        void new_data(const std::string& key, const std::string& value);
    };

}
}

#endif
