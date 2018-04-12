/**
 * \file witchw/WitchTime.hpp
 * \brief Magic definitions for handling time measurements.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef LIB_WITCHW__WITCH_TIME_HPP
#define LIB_WITCHW__WITCH_TIME_HPP

#include <string>
#include <chrono>
#include <map>

namespace witchw {

    /** \brief Time measuring magic clock. */
    class wClock {
        std::map<std::string, std::chrono::high_resolution_clock::time_point> registered_cts;
        std::string selected_dunit = "extended";
    public:
        /** \brief Associate current time to a tag. */
        void registerTime(const std::string key);
        /** \brief Select a duration output unit. \returns The selected unit. */
        std::string selectDurationUnit(const std::string unit);
        /** \brief Compute the duration (in nanoseconds) between too registered clock times */
        std::string nanoseconds (const std::string origin, const std::string target);
        /** \brief Compute the duration (in microseconds) between too registered clock times */
        std::string microseconds(const std::string origin, const std::string target);
        /** \brief Compute the duration (in milliseconds) between too registered clock times */
        std::string milliseconds(const std::string origin, const std::string target);
        /** \brief Compute the duration (in seconds) between too registered clock times */
        std::string seconds     (const std::string origin, const std::string target);
        /** \brief Compute the duration (in minutes) between too registered clock times */
        std::string minutes     (const std::string origin, const std::string target);
        /** \brief Compute the duration (in hours) between too registered clock times */
        std::string hours       (const std::string origin, const std::string target);
        /** \brief Compute the duration (extended seconds) between two registered clock times */
        std::string extseconds  (const std::string origin, const std::string target);
        /** \brief Compute the duration (extended) between two registered clock times */
        std::string extended    (const std::string origin, const std::string target);
        /** \brief Compute the duration (in the selected format) between two registered clock times */
        std::string duration    (const std::string origin, const std::string target);
    };

}

#endif
