#define LIB_WHY3CPP__PARSERS_SANITIZE_CPP

#include <snlog/snlog.hpp>
#include <smtlib2tools/parser-command.hpp>
#include <stdutils/collections.hpp>
#include <why3cpp/why3proofutils.hpp>

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

    class DeclReorderer : public smtlib2::SMTl2CommandHandler {
        std::stringstream ss;
        const std::map<std::string, std::string>& reorders;

        bool substitute(const std::string& cmd, const std::string& data);
    public:
        DeclReorderer(const std::map<std::string, std::string>& reorders);

        inline strptr getReorderedScript() const
        { return strptr(new std::string(ss.str())); }
    };

    static inline std::map<std::string, std::string> build_reorders(const std::set<std::string>& fundecls);

}

using namespace why3cpp;

Sanitizer::Sanitizer() {
    handlers["assert"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-const"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-datatype"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-datatypes"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-fun"] = std::bind(&Sanitizer::sfundecl, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-sort"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["define-fun"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["define-fun-rec"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["define-funs-rec"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["define-sort"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["set-info"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);
    handlers["set-option"] = std::bind(&Sanitizer::keep, this, std::placeholders::_1, std::placeholders::_2);

    handlers["check-sat"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["check-sat-assuming"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["echo"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["exit"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-assertions"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-assignment"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-info"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-model"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-option"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-proof"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-unsat-assumptions"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-unsat-core"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-value"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["pop"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["push"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["reset"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);
    handlers["reset-assertions"] = std::bind(&Sanitizer::sanitize, this, std::placeholders::_1, std::placeholders::_2);

    handlers["set-logic"] = std::bind(&Sanitizer::setlogic, this, std::placeholders::_1, std::placeholders::_2);
}

DeclReorderer::DeclReorderer(const std::map<std::string, std::string>& reorders)
    : reorders(reorders) {
    handlers["assert"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-const"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-datatype"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-datatypes"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-fun"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["declare-sort"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["define-fun"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["define-fun-rec"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["define-funs-rec"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["define-sort"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["set-info"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["set-option"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["check-sat"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["check-sat-assuming"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["echo"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["exit"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-assertions"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-assignment"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-info"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-model"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-option"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-proof"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-unsat-assumptions"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-unsat-core"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["get-value"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["pop"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["push"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["reset"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["reset-assertions"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
    handlers["set-logic"] = std::bind(&DeclReorderer::substitute, this, std::placeholders::_1, std::placeholders::_2);
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

const std::string extract_declname(const std::string& data) {
    size_t dpos = 0;
    while (data.at(dpos++) == ' ');
    size_t npos = --dpos;
    while (data.at(npos++) != ' ');
    return data.substr(dpos, npos-1-dpos);
}

bool Sanitizer::sfundecl(const std::string& cmd, const std::string& data) {
    ss << smtlib2::SMTl2CommandWrapper(cmd, data) << '\n';
    fundecls.insert(extract_declname(data));
    return true;
}

static inline void replace_var(std::string& data, const std::string& source, const std::string& target) {
    std::map<std::string, std::string> vreps;
    vreps["(" + source + " "] = "(" + target + " ";
    vreps["(" + source + ")"] = "(" + target + ")";
    vreps[" " + source + ")"] = " " + target + ")";
    vreps[" " + source + " "] = " " + target + " ";
    for (auto vrep : vreps) {
        size_t pos = data.find(vrep.first);
        while (pos != std::string::npos) {
            data.replace(pos, vrep.first.length(), vrep.second);
            pos = data.find(vrep.first);
        }
    }
    /* Additional pre-preplacements */
    if (data.find(source + " ") == 0) {
        data.replace(0, source.length(), target);
    }
}

static inline void substitute_pair(std::string& data, const std::pair<std::string, std::string>& reop) {
    replace_var(data, reop.first, TEMPORARY_REPLACEMENT_STRING);
    replace_var(data, reop.second, reop.first);
    replace_var(data, TEMPORARY_REPLACEMENT_STRING, reop.second);
}

bool DeclReorderer::substitute(const std::string& cmd, const std::string& data) {
    ss << "(" << cmd << " ";
    std::string workable = data;
    for (auto srdata : reorders)
        substitute_pair(workable, srdata);
    ss << workable << ")" << '\n';
    return true;
}

struct DisambResult {
    const std::string source;
    const uint32_t disamb;
};

static inline constexpr bool is_num(const char c) {
    return c == '0' || c == '1' || c == '2' || c == '3' || c == '4'
        || c == '5' || c == '6' || c == '7' || c == '8' || c == '9';
}

static inline const DisambResult analyze_disamb(const std::string& val) {
    size_t dpos = val.length();
    while (dpos > 0) {
        if (!is_num(val[--dpos])) {
            dpos++;
            break;
        }
    }
    const std::string source = val.substr(0, dpos);
    const uint32_t disamb = std::atoi(val.substr(dpos, val.length() - dpos).c_str());
    return DisambResult({ source, disamb });
}

static inline std::map<std::string, std::string>
why3cpp::build_reorders(const std::set<std::string>& fundecls) {
    std::map<std::string, std::set<uint32_t>> disambs;
    for (const std::string& fname : fundecls) {
        const DisambResult res = analyze_disamb(fname);
        if (!stdutils::inmap(disambs, res.source)) {
            disambs[res.source] = std::set<uint32_t>();
        }
        disambs.at(res.source).insert(res.disamb);
    }

    std::map<std::string, std::string> reorders;
    for (const std::pair<std::string, std::set<uint32_t>>& dpair : disambs) {
        if (dpair.second.size() > 1) {
            uint32_t maxd = *(dpair.second.rbegin());
            const std::string disambed = dpair.first + std::to_string(maxd);
            reorders[dpair.first] = disambed;
        }
    }
    return reorders;
}

extern strptr why3cpp::vc_sanitization(strptr data, bool reoder) {
    Sanitizer sanitizer;
    smtlib2::SMTl2CommandParser cparser(data);
    cparser.parse(sanitizer);
    auto reorders = build_reorders(sanitizer.getFunDecls());
    if (!reoder || reorders.empty())
        return sanitizer.getSanitizedScript();
    DeclReorderer reorderer(reorders);
    smtlib2::SMTl2CommandParser rparser(sanitizer.getSanitizedScript());
    rparser.parse(reorderer);
    return reorderer.getReorderedScript();
}
