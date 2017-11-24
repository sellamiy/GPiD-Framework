/**
 * \file witchw/WitchControl.hpp
 * \brief Magic definitions for controlling witches.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef LIB_WITCHW__WITCH_CONTROL_HPP
#define LIB_WITCHW__WITCH_CONTROL_HPP

#include <witchw/WitchPrinters.hpp>
#include <witchw/WitchTime.hpp>

namespace witchw {

    /** \brief Main controller. */
    struct wController {
        wStatistics stats;
        wClock time;
    };

}

#endif
