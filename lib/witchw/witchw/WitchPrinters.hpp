#ifndef LIB_WITCHW__WITCH_PRINTERS_HPP
#define LIB_WITCHW__WITCH_PRINTERS_HPP

#include <cstdint>
#include <string>
#include <list>
#include <iostream>

namespace witchw {

    struct wStatisticData {
        const std::string key;
        const std::string data;
        const uint32_t level;
        wStatisticData(std::string key, std::string data, uint32_t level = 1)
            : key(key), data(data), level(level) {}
        wStatisticData(const wStatisticData& cpy)
            : key(cpy.key), data(cpy.data), level(cpy.level) {}
    };

    struct wStatistics {
        const std::string wStatisticsHeader =
            "----------------------------------------------------\n"
            "-------------------- Statistics --------------------\n"
            "----------------------------------------------------\n\n";
        const std::string wStatisticsFooter =
            "\n----------------------------------------------------\n";
        std::list<wStatisticData> stats;
        inline void addStatistic(const wStatisticData& s) { stats.push_back(s); }
        inline void addStatisticGroup()
        { if (stats.size() > 0) stats.push_back(wStatisticData("", "", 0)); }
        template <typename printable>
        inline void addStatistic(const std::string key, const printable data, const uint32_t level = 1)
        {
            std::stringstream dvalue;
            dvalue << data;
            const wStatisticData std(key, dvalue.str(), level);
            stats.push_back(std);
        }
    };

    inline std::ostream& operator<<(std::ostream& out, const wStatisticData& d) {
        if (d.level == 0) return out << std::endl;
        for (uint32_t i = 0; i < d.level; i++) out << " ";
        return out << "> " << d.key << " : " << d.data << std::endl;
    }

    inline std::ostream& operator<<(std::ostream& out, const std::list<wStatisticData>& l) {
        for (wStatisticData d : l) out << d;
        return out;
    }

    inline std::ostream& operator<<(std::ostream& out, const wStatistics& d) {
        return out << d.wStatisticsHeader << d.stats << d.wStatisticsFooter;
    }

}

#endif
