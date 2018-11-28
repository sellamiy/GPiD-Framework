#define LIB_SMTLIB2_LITERAL_TOOLS__CORE__CPP

#include <sstream>
#include <smtlit/smtlit-config.hpp>

using namespace smtlit;

extern smtlit_t smtlit::apply(const smtfun_t& f, const smtparam_binding_set& params) {
    std::stringstream ss;
    ss << "(" << ident(f);
    for (smtparam_size_t param = 0; param < plist(f).size(); ++param)
        ss << " " << params.at(param);
    ss << ")";
    return smtlit_t(ss.str(), rtype(f));
}
