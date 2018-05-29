/**
 * \defgroup gpidinstrumentlib GPiD-Framework Instrumentation Utilities
 * \brief Intrumentation utilities for algorithms analyses.
 * \file gpid/instrument/instrument.hpp
 * \brief GPiD-Framework Core Header.
 * \ingroup gpidinstrumentlib
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__INSTRUMENT__INSTRUMENT_HPP
#define GPID_FRAMEWORK__INSTRUMENT__INSTRUMENT_HPP
#include <gpid/util/instrument_controller.hpp>
namespace gpid {
namespace instrument {

    enum class instloc {
        stack_push, stack_pop,
        pre_select, implicate, skip,
        ismt_test, ismt_result,
        reset, end
    };

#ifdef GPID_INSTRUMENTATION

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
#define insthandle(data, location) gpid::instrument::analyze_data((data), (location))
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
