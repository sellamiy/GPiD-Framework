#define GPID_FRAMEWORK__CORE__ALGORITHM_CPP

#include <gpid/core/algorithm.hpp>
#include <gpid/instrument/instrument.hpp>

using namespace gpid;

void GPiDAlgorithm::execute() {
    registerInterruptionHandlers(&iflags);
    startTimeout(&iflags, options.core.time_limit);
    _execute();
    stopTimeout();
    restoreInterruptionHandlers();
    insthandle(instrument::idata(), instrument::instloc::end);
}
