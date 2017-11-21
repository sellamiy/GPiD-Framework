#ifndef LIB_WITCHW__WITCH_CONTROL_HPP
#define LIB_WITCHW__WITCH_CONTROL_HPP

#include <witchw/WitchPrinters.hpp>
#include <witchw/WitchTime.hpp>

namespace witchw {

    struct wController {
        wStatistics stats;
        wClock time;
    };

}

#endif
