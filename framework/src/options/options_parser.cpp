#define GPID_OPTIONS_PARSER

#include <snlog/snlog.hpp>
#include <gpid/options/options_core.hpp>

extern gpid::OptionStatus gpid::parseOptions(CoreOptions& opts, char** data) {
    snlog::l_warn("Options parser not implemented!");
    return OptionStatus::OK;
}
