#define LIB_SMTLIB2_CPP_TOOLS__CORE__CPP

#include <sstream>
#include <smtlib2tools/core.hpp>

using namespace smtlib2;

extern smtlit_t smtlib2::apply(const smtfun_t& f, const smtparam_binding_set& params) {
    std::stringstream ss;
    ss << "(" << ident(f);
    for (smtparam_size_t param = 0; param < plist(f).size(); ++param)
        ss << " " << params.at(param);
    ss << ")";
    return smtlit_t(ss.str(), rtype(f));
}
