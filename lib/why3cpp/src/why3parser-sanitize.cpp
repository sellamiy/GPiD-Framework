#define LIB_WHY3CPP__PARSERS_SANITIZE_CPP

#include <snlog/snlog.hpp>
#include <smtlib2tools/parser-command.hpp>
#include <why3cpp/why3proofutils.hpp>

using strptr = std::shared_ptr<std::string>;

namespace why3cpp {

    class Sanitizer : public smtlib2::SMTl2CommandHandler {
        std::stringstream ss;

        bool keep(const smtlib2::SMTl2Command& cmd);
        bool sanitize(const smtlib2::SMTl2Command& cmd);
        bool setlogic(const smtlib2::SMTl2Command& cmd);
    public:
        Sanitizer();

        inline strptr getSanitizedScript() const
        { return strptr(new std::string(ss.str())); }
    };

}

using namespace why3cpp;

Sanitizer::Sanitizer() {
    handlers["assert"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["declare-const"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["declare-datatype"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["declare-datatypes"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["declare-fun"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["declare-sort"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["define-fun"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["define-fun-rec"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["define-funs-rec"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["define-sort"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["set-info"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);
    handlers["set-option"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1);

    handlers["check-sat"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["check-sat-assuming"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["echo"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["exit"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["get-assertions"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["get-assignment"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["get-info"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["get-model"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["get-option"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["get-proof"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["get-unsat-assumptions"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["get-unsat-core"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["get-value"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["pop"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["push"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["reset"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);
    handlers["reset-assertions"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1);

    handlers["set-logic"] = std::bind(&Sanitizer::setlogic, this, std::placeholders::_1);
}

bool Sanitizer::keep(const smtlib2::SMTl2Command& cmd) {
    ss << cmd << '\n'; return true;
}

bool Sanitizer::sanitize(const smtlib2::SMTl2Command&) {
    return true;
}

bool Sanitizer::setlogic(const smtlib2::SMTl2Command&) {
    ss << "(set-logic ALL)" << '\n' ; return true;
}

extern strptr why3cpp::vc_sanitization(strptr data) {
    smtlib2::StringMemory smem;
    Sanitizer sanitizer;
    smtlib2::SMTl2CommandParser cparser(data, smem);
    cparser.initialize();
    cparser.parse(sanitizer);
    return sanitizer.getSanitizedScript();
}
