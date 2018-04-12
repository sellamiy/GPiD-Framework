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

    template <typename duration_type, typename cycle_type>
    static inline string dcyt_duration
    (map<string, chrono::high_resolution_clock::time_point>& registered_cts,
     const string origin, const string target) {
        chrono::high_resolution_clock::time_point to = registered_cts[origin];
        chrono::high_resolution_clock::time_point tt = registered_cts[target];
        auto duration = chrono::duration_cast<duration_type>((tt-to) % cycle_type(1));
        stringstream str; str << duration.count();
        return str.str();
    }

    void wClock::registerTime(const string key) {
        chrono::high_resolution_clock::time_point tp = chrono::high_resolution_clock::now();
        registered_cts[key] = tp;
    }

    string wClock::selectDurationUnit(const string unit) {
        if (unit == "nanoseconds")  selected_dunit = unit;
        if (unit == "microseconds") selected_dunit = unit;
        if (unit == "milliseconds") selected_dunit = unit;
        if (unit == "seconds")      selected_dunit = unit;
        if (unit == "minutes")      selected_dunit = unit;
        if (unit == "hours")        selected_dunit = unit;
        if (unit == "extseconds")   selected_dunit = unit;
        if (unit == "extended")     selected_dunit = unit;
        return unit;
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
    string wClock::extseconds(const string origin, const string target) {
        return dcst_duration<chrono::seconds>(registered_cts, origin, target) + "."
            + dcyt_duration<chrono::milliseconds, chrono::seconds>(registered_cts, origin, target) + " s";
    }
    string wClock::extended(const string origin, const string target) {
        string d_h  = dcst_duration<chrono::hours>(registered_cts, origin, target);
        string d_m  = dcyt_duration<chrono::minutes, chrono::hours>(registered_cts, origin, target);
        string d_s  = dcyt_duration<chrono::seconds, chrono::minutes>(registered_cts, origin, target);
        string d_ms = dcyt_duration<chrono::milliseconds, chrono::seconds>(registered_cts, origin, target);
        string dstr = "";
        if (d_h  != "0") dstr += d_h  + " h ";
        if (d_m  != "0") dstr += d_m  + " m ";
        dstr += d_s;
        if (d_ms != "0") dstr += "." + d_ms + " s ";
        return dstr;
    }
    string wClock::duration(const string origin, const string target) {
        if (selected_dunit == "nanoseconds")  return nanoseconds(origin, target);
        if (selected_dunit == "microseconds") return microseconds(origin, target);
        if (selected_dunit == "milliseconds") return milliseconds(origin, target);
        if (selected_dunit == "seconds")      return seconds(origin, target);
        if (selected_dunit == "minutes")      return minutes(origin, target);
        if (selected_dunit == "hours")        return hours(origin, target);
        if (selected_dunit == "extseconds")   return extseconds(origin, target);
        if (selected_dunit == "extended")     return extended(origin, target);
        // Corrupted unit, switching back to default. TODO: Log this error
        selected_dunit = "extended";
        return extended(origin, target);
    }

}
