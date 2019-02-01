/**
 * \file abdulot/instrument/instrument.hpp
 * \brief Abdulot-Framework Core Header.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT_FRAMEWORK__INSTRUMENT__INSTRUMENT_HPP
#define ABDULOT_FRAMEWORK__INSTRUMENT__INSTRUMENT_HPP

#include <abdulot/instrument/controller.hpp>

namespace abdulot {
namespace instrument {

    enum class instloc {
        stack_push, stack_pop,
        pre_select, implicate, skip,
        ismt_test, ismt_result,
        reset, end
    };

#ifdef INSTRUMENTATION

    class idata {
        const std::string data;
    public:
        const std::string get() const { return data; }

        idata()                    : data("")                {}
        idata(const idata& other)  : data(other.data)        {}
        idata(const std::string s) : data(s)                 {}
        idata(const uint32_t i)    : data(std::to_string(i)) {}
    };

    extern void initialize(InstrumentOptions& opts, InstrumentController& ctrler);
    extern void analyze_data(const idata data, instloc location);
#define insthandle(data, location) abdulot::instrument::analyze_data((data), (location))
    extern void finalize(InstrumentOptions& opts, InstrumentController& ctrler);

#else

    static inline bool idata()                  { return true; }
    static inline bool idata(const std::string) { return true; }
    static inline bool idata(const uint32_t)    { return true; }

    static inline void initialize(InstrumentOptions&, InstrumentController&) {}
#define insthandle(data, location)
    static inline void finalize(InstrumentOptions&, InstrumentController&) {}

#endif
}
}
#endif
