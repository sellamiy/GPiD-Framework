/**
 * \file witchw/WitchPrinters.hpp
 * \brief Magic definitions for printing statistics.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef LIB_WITCHW__WITCH_PRINTERS_HPP
#define LIB_WITCHW__WITCH_PRINTERS_HPP

#include <cstdint>
#include <string>
#include <list>
#include <iostream>
#include <sstream>

namespace witchw {

    /** \brief A printable statistic */
    struct wStatisticData {
        /** \brief Statistic name */
        const std::string key;
        /** \brief Statistic value */
        const std::string data;
        /** \brief Statistic depth level */
        const uint32_t level;
        /** \brief Initializing constructor */
        wStatisticData(std::string key, std::string data, uint32_t level = 1)
            : key(key), data(data), level(level) {}
        /** \brief Copy constructor */
        wStatisticData(const wStatisticData& cpy)
            : key(cpy.key), data(cpy.data), level(cpy.level) {}
    };

    /** \brief A set of printable statistics */
    struct wStatistics {
        /** \brief Header message */
        const std::string wStatisticsHeader =
            "----------------------------------------------------\n"
            "-------------------- Statistics --------------------\n"
            "----------------------------------------------------\n\n";
        /** \brief Footer message */
        const std::string wStatisticsFooter =
            "\n----------------------------------------------------\n";
        /** \brief Statistics to print */
        std::list<wStatisticData> stats;
        /** \brief Add a new statistic to the current group. */
        inline void addStatistic(const wStatisticData& s) { stats.push_back(s); }
        /** \brief Create a new group of statistics. */
        inline void addStatisticGroup()
        { if (stats.size() > 0) stats.push_back(wStatisticData("", "", 0)); }

        /** \brief Create and add a new statistic to the current group. */
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
        return out << "(*) " << d.key << " : " << d.data << std::endl;
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
