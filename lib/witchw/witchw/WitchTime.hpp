#ifndef _WITCHW_TIME_
#define _WITCHW_TIME_

#include <string>
#include <chrono>
#include <map>

namespace witchw {

    class wClock {
        std::map<std::string, std::chrono::high_resolution_clock::time_point> registered_cts;
    public:
        void registerTime(const std::string key);
        std::string nanoseconds (const std::string origin, const std::string target);
        std::string microseconds(const std::string origin, const std::string target);
        std::string milliseconds(const std::string origin, const std::string target);
        std::string seconds     (const std::string origin, const std::string target);
        std::string minutes     (const std::string origin, const std::string target);
        std::string hours       (const std::string origin, const std::string target);
    };

}

#endif
