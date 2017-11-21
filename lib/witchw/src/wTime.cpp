#define LIB_WITCHW__WTIME_CPP

#include <map>
#include <sstream>
#include <iostream>

#include <witchw/WitchTime.hpp>

using namespace std;

namespace witchw {

    template <typename duration_type>
    static inline string dcst_duration
    (map<string, chrono::high_resolution_clock::time_point>& registered_cts,
     const string origin, const string target) {
        chrono::high_resolution_clock::time_point to = registered_cts[origin];
        chrono::high_resolution_clock::time_point tt = registered_cts[target];
        auto duration = chrono::duration_cast<duration_type>(tt-to);
        stringstream str; str << duration.count();
        return str.str();
    }

    void wClock::registerTime(const string key) {
        chrono::high_resolution_clock::time_point tp = chrono::high_resolution_clock::now();
        registered_cts[key] = tp;
    }

    string wClock::nanoseconds(const string origin, const string target) {
        return dcst_duration<chrono::nanoseconds>(registered_cts, origin, target) + " ns";
    }
    string wClock::microseconds(const string origin, const string target) {
        return dcst_duration<chrono::microseconds>(registered_cts, origin, target) + " µs";
    }
    string wClock::milliseconds(const string origin, const string target) {
        return dcst_duration<chrono::milliseconds>(registered_cts, origin, target) + " ms";
    }
    string wClock::seconds(const string origin, const string target) {
        return dcst_duration<chrono::seconds>(registered_cts, origin, target) + " s";
    }
    string wClock::minutes(const string origin, const string target) {
        return dcst_duration<chrono::minutes>(registered_cts, origin, target) + " m";
    }
    string wClock::hours(const string origin, const string target) {
        return dcst_duration<chrono::hours>(registered_cts, origin, target) + " h";
    }

}
