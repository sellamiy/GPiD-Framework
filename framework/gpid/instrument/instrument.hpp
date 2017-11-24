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
    enum analyze_type { stack_push, stack_pop, pre_select, implicate, model_skip, reset, end };
#ifdef GPID_INSTRUMENTATION
    extern void initialize(InstrumentOptions& opts, InstrumentController& ctrler);
    extern void analyze(void* data, analyze_type analysis);
    extern void finalize(InstrumentOptions& opts, InstrumentController& ctrler);
#else
    static inline void initialize(InstrumentOptions&, InstrumentController&) {}
    static inline void analyze(void*, analyze_type)  {}
    static inline void finalize(InstrumentOptions&, InstrumentController&) {}
#endif
}
}
#endif
