#ifndef GPID_INSTRUMENT_HPP
#define GPID_INSTRUMENT_HPP
#include <gpid/config.hpp>
#include <gpid/options/options_instrument.hpp>
#include <gpid/util/instrument_controller.hpp>
#include <iostream>
namespace gpid {
namespace instrument {
    enum analyze_type { stack_push, stack_pop, pre_select, model_skip, reset, end };
#ifdef GPID_INSTRUMENTATION
    extern void initialize(InstrumentOptions& opts, InstrumentController& ctrler);
    extern void analyze(void* data, analyze_type analysis);
    extern void finalize(InstrumentOptions& opts, InstrumentController& ctrler);
#else
    static inline void initialize(InstrumentsOption&, InstrumentController&) {}
    static inline void analyze(void*, analyze_type)  {}
    static inline void finalize(InstrumentOptions& opts, InstrumentController& ctrler) {}
#endif
}
}
#endif
