#define LIB_WHY3CPP__PARSERS_SANITIZE_CPP

#include <snlog/snlog.hpp>
#include <smtlib2tools/parser-command.hpp>
#include <stdutils/collections.hpp>
#include <why3cpp/why3proofutils.hpp>
#include <why3cpp/why3vcinject.hpp>

#define TEMPORARY_REPLACEMENT_STRING "____TRS____"

using strptr = std::shared_ptr<std::string>;

namespace why3cpp {

    class Sanitizer : public smtlib2::SMTl2CommandHandler {
        std::stringstream ss;
        std::set<std::string> fundecls;

        bool keep(const std::string& cmd, const std::string& data);
        bool sanitize(const std::string& cmd, const std::string& data);
        bool setlogic(const std::string& cmd, const std::string& data);
        bool sfundecl(const std::string& cmd, const std::string& data);
    public:
        Sanitizer();

        inline strptr getSanitizedScript() const
        { return strptr(new std::string(ss.str())); }

        inline const std::set<std::string>& getFunDecls() const
        { return fundecls; }
    };

    class DeclInjector : public smtlib2::SMTl2CommandHandler {
        std::stringstream ss;
        const VCInjectionMode mode;
        const std::set<std::string>& injectables;
        const std::set<std::string>& decls;

        bool forward(const std::string& cmd, const std::string& data);
        bool inject(const std::string& cmd, const std::string& data);
    public:
        DeclInjector(const VCInjectionMode mode,
                     const std::set<std::string>& injectables, const std::set<std::string>& decls);

        inline strptr getInjectedScript() const { return strptr(new std::string(ss.str())); }
    };

    static inline std::set<std::string> build_injectables(const std::set<std::string>& fundecls);

}

using namespace why3cpp;

Sanitizer::Sanitizer() {
    handlers["assert"]                = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-const"]         = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-datatype"]      = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-datatypes"]     = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-fun"]           = std::bind(&Sanitizer::sfundecl, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-sort"]          = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["define-fun"]            = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["define-fun-rec"]        = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["define-funs-rec"]       = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["define-sort"]           = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["set-info"]              = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["set-option"]            = std::bind(&Sanitizer::keep, this,
                                                  std::placeholders::_1, std::placeholders::_2);

    handlers["check-sat"]             = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["check-sat-assuming"]    = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["echo"]                  = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["exit"]                  = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-assertions"]        = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-assignment"]        = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-info"]              = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-model"]             = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-option"]            = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-proof"]             = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-unsat-assumptions"] = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-unsat-core"]        = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-value"]             = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["pop"]                   = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["push"]                  = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["reset"]                 = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["reset-assertions"]      = std::bind(&Sanitizer::sanitize, this,
                                                  std::placeholders::_1, std::placeholders::_2);

    handlers["set-logic"]             = std::bind(&Sanitizer::setlogic, this,
                                                  std::placeholders::_1, std::placeholders::_2);
}

DeclInjector::DeclInjector
(const VCInjectionMode mode, const std::set<std::string>& injectables, const std::set<std::string>& decls)
    : mode(mode), injectables(injectables), decls(decls) {
    handlers["assert"]                = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-const"]         = std::bind(&DeclInjector::inject, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-datatype"]      = std::bind(&DeclInjector::inject, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-datatypes"]     = std::bind(&DeclInjector::inject, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-fun"]           = std::bind(&DeclInjector::inject, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["declare-sort"]          = std::bind(&DeclInjector::inject, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["define-fun"]            = std::bind(&DeclInjector::inject, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["define-fun-rec"]        = std::bind(&DeclInjector::inject, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["define-funs-rec"]       = std::bind(&DeclInjector::inject, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["define-sort"]           = std::bind(&DeclInjector::inject, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["set-info"]              = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["set-option"]            = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["check-sat"]             = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["check-sat-assuming"]    = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["echo"]                  = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["exit"]                  = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-assertions"]        = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-assignment"]        = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-info"]              = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-model"]             = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-option"]            = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-proof"]             = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-unsat-assumptions"] = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-unsat-core"]        = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["get-value"]             = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["pop"]                   = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["push"]                  = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["reset"]                 = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["reset-assertions"]      = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
    handlers["set-logic"]             = std::bind(&DeclInjector::forward, this,
                                                  std::placeholders::_1, std::placeholders::_2);
}

bool Sanitizer::keep(const std::string& cmd, const std::string& data) {
    ss << smtlib2::SMTl2CommandWrapper(cmd, data) << '\n'; return true;
}

bool Sanitizer::sanitize(const std::string&, const std::string&) {
    return true;
}

bool Sanitizer::setlogic(const std::string&, const std::string&) {
    ss << "(set-logic ALL)" << '\n' ; return true;
}

static inline constexpr bool is_whitespace(char c) {
    return c == ' ' || c == '\n' || c == '\t';
}

const std::string extract_declname(const std::string& data) {
    size_t dpos = 0;
    while (is_whitespace(data.at(dpos++)));
    size_t npos = --dpos;
    while (!is_whitespace(data.at(npos++)));
    return data.substr(dpos, npos-1-dpos);
}

bool Sanitizer::sfundecl(const std::string& cmd, const std::string& data) {
    ss << smtlib2::SMTl2CommandWrapper(cmd, data) << '\n';
    fundecls.insert(extract_declname(data));
    return true;
}

bool DeclInjector::forward(const std::string& cmd, const std::string& data) {
    ss << smtlib2::SMTl2CommandWrapper(cmd, data) << '\n'; return true;
}

bool DeclInjector::inject(const std::string& cmd, const std::string& data) {
    ss << smtlib2::SMTl2CommandWrapper(cmd, data) << '\n';
    const std::string declname = extract_declname(data);
    if (stdutils::inset(injectables, declname)) {
        vcinject(ss, mode, declname, decls);
    }
    return true;
}

struct DisambResult {
    const std::string source;
    const uint32_t disamb;
};

static inline std::set<std::string>
why3cpp::build_injectables(const std::set<std::string>& fundecls) {
    std::set<std::string> injectables;
    for (const std::string& decl : fundecls)
        if (vcinjectable(decl, fundecls))
            injectables.insert(decl);
    return injectables;
}

extern strptr why3cpp::vc_sanitization(strptr data, bool inject, VCInjectionMode injectmode) {
    Sanitizer sanitizer;
    smtlib2::SMTl2CommandParser cparser(data);
    cparser.parse(sanitizer);
    std::set<std::string> injectables = build_injectables(sanitizer.getFunDecls());
    if (!inject || injectables.empty())
        return sanitizer.getSanitizedScript();
    DeclInjector seringe(injectmode, injectables, sanitizer.getFunDecls());
    smtlib2::SMTl2CommandParser iparser(sanitizer.getSanitizedScript());
    iparser.parse(seringe);
    return seringe.getInjectedScript();
}
