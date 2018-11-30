/**
 * \file stdutils/stats-controller.hpp
 * \brief Statistics controller.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef LIB_STANDARD_UTILS__STATS_CONTROL_HPP
#define LIB_STANDARD_UTILS__STATS_CONTROL_HPP

#include <stdutils/stats-printer.hpp>
#include <stdutils/time.hpp>

namespace stdutils {

    /** \brief Main controller. */
    struct StatisticController {
        StatisticPrinter stats;
        StdClock time;
    };

}

#endif
