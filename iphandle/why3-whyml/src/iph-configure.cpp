#define WHY3_WHYML_IPH_FOR_GPID__IPH_CONFIGURE_OPTIONS__CPP

#include <cmath>
#include <why3-whyml-iph.hpp>

using namespace abdulot;

void W3WML_IPH::configure(abdulot::ilinva::IlinvaOptions& opts) {
    const std::string& opt_tlim = W3WML_ProblemController::w3opt_tlim;
    if (stdutils::ninmap(opts.handler_options, opt_tlim)) {
        if (opts.smt_time_limit > 0) {
            opts.handler_options[opt_tlim] = std::to_string(opts.smt_time_limit);
        } else if (opts.small_smt_time_limit > 0) {
            opts.handler_options[opt_tlim] = std::to_string(std::round(opts.small_smt_time_limit));
        } else {
            opts.handler_options[opt_tlim] = std::to_string(WHY3_DEFAULT_SOLVER_TLIM);
        }
    }
}
