#define GPID_FRAMEWORK__CORE__ALGORITHM_CPP

#include <snlog/snlog.hpp>
#include <gpid/core/algorithm.hpp>
#include <gpid/instrument/instrument.hpp>

using namespace gpid;

void GPiDAlgorithm::_terminate_execution() {
    _execute();
    stopTimeout();
    restoreInterruptionHandlers();
    insthandle(instrument::idata(), instrument::instloc::end);
}

void GPiDAlgorithm::execute(bool in_thread) {
    registerInterruptionHandlers(&iflags);
    startTimeout(&iflags, options.core.time_limit);
    if (in_thread) {
        execution_thread = std::unique_ptr<std::thread>
            (new std::thread( [this] { _terminate_execution(); }));
    } else {
        _terminate_execution();
    }
}

void GPiDAlgorithm::interrupt() {
    iflags.interrupt(SystemInterruptionFlags::Reason::__PARENT);
}

void GPiDAlgorithm::join() {
    if (execution_thread) {
        if (execution_thread->joinable()) {
            execution_thread->join();
        } else {
            snlog::l_error("Thread algorithm instance not joinable");
        }
    } else {
        snlog::l_error("Trying to join non-threaded algorithm instance");
    }
}
