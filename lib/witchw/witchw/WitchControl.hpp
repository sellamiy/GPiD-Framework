#ifndef _WITCHW_CONTROL_
#define _WITCHW_CONTROL_

#include <witchw/WitchPrinters.hpp>
#include <witchw/WitchTime.hpp>

namespace witchw {

    struct wController {
        wStatistics stats;
        wClock time;
    };

}

#endif
