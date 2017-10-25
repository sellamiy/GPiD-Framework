#define GPID_CONTROLLERS_CONSTRUCTORS

#include <snlog/snlog.hpp>
#include <gpid/util/skipper_controller.hpp>

using namespace snlog;
using namespace gpid;

SkipperController::SkipperController(const CoreOptions& opts) :
    storage(opts.engine.store_implicates)
{ }

SkipperController::SkipperController(const SkipperController& ctrler) :
    storage(ctrler.storage)
{ }
