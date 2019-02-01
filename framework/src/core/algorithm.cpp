#define ABDULOT__CORE__ALGORITHM_CPP

#include <snlog/snlog.hpp>
#include <abdulot/core/algorithm.hpp>
#include <abdulot/instrument/instrument.hpp>

using namespace abdulot;

void Algorithm::_terminate_execution() {
    _execute();
    stopTimeout();
    restoreInterruptionHandlers();
    insthandle(instrument::idata(), instrument::instloc::end);
    _execution_complete = true;
}

void Algorithm::execute(bool in_thread) {
    registerInterruptionHandlers(&iflags);
    startTimeout(&iflags, options.core.time_limit);
    if (in_thread) {
        execution_thread = std::unique_ptr<std::thread>
            (new std::thread( [this] { _terminate_execution(); }));
    } else {
        _terminate_execution();
    }
}

void Algorithm::interrupt() {
    iflags.interrupt(SystemInterruptionFlags::Reason::__PARENT);
}

void Algorithm::join() {
    if (execution_thread) {
        if (execution_thread->joinable()) {
            execution_thread->join();
        } else {
            snlog::l_error() << "Thread algorithm instance not joinable" << snlog::l_end;
        }
    } else {
        snlog::l_error() << "Trying to join non-threaded algorithm instance" << snlog::l_end;
    }
}
