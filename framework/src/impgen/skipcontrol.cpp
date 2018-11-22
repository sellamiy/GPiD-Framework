#define GPID_FRAMEWORK__IMPGEN__SKIP_CONTROL_CPP

#include <fstream>
#include <gpid/impgen/skipcontrol.hpp>

using namespace gpid;

SkipController::SkipController(const ImpgenOptions& opts) :
    storage(opts.store_implicates),
    max_level(opts.max_level),
    inconsistencies(opts.allow_inconsistencies),
    consequences(opts.detect_consequences),
    additionals(opts.additional_checker)
{ }

SkipController::SkipController(const SkipController& ctrler) :
    storage(ctrler.storage),
    max_level(ctrler.max_level),
    inconsistencies(ctrler.inconsistencies),
    consequences(ctrler.consequences),
    additionals(ctrler.additionals)
{ }
