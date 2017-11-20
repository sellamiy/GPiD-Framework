#define Z3_CONTEXT

#include <snlog/snlog.hpp>
#include <gpid/solvers-wrap/cvc4_context.hpp>

using namespace snlog;

namespace gpid {
namespace stringUtils {
    static inline void ltrim(std::string &s) {
        s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](int ch) {
                    return !std::isspace(ch);
                }));
    }
    static inline void rtrim(std::string &s) {
        s.erase(std::find_if(s.rbegin(), s.rend(), [](int ch) {
                    return !std::isspace(ch);
                }).base(), s.end());
    }
    static inline void trim(std::string &s) {
        ltrim(s);
        rtrim(s);
    }

    template<typename Out>
    static inline void split(const std::string &s, char delim, Out result) {
        std::stringstream ss(s);
        std::string item;
        while (std::getline(ss, item, delim)) {
            trim(item);
            if (item != "") {
                *(result++) = item;
            }
        }
    }
    static inline std::vector<std::string> split(const std::string &s, char delim) {
        std::vector<std::string> elems;
        split(s, delim, std::back_inserter(elems));
        return elems;
    }
    static inline std::string first(const std::string &s, char delim)
    { return split(s, delim)[0]; }
    static inline std::string second(const std::string &s, char delim)
    { return split(s, delim)[1]; }
}
namespace cvc4Utils {

    const std::set<std::string> cvc4CommandsList =
        {
            "ASSERT",
            "CHECKSAT",
            "COUNTEREXAMPLE",
            "COUNTERMODEL",
            "DATATYPE",
            "OPTION",
            "POP",
            "PUSH",
            "QUERY",
            "RESTART",
            "PRINT",
            "TRANSFORM",
            "WHERE",
            "ECHO",
            "INCLUDE",
            "TRACE",
            "UNTRACE"
        };

    class CVC4DeclBrowser {
        const std::string browsed_command;
        bool isComment() const
        { return browsed_command.size() > 0 && browsed_command[0] == '%'; }
        bool isNonDeclarativeCommand() const
        { return cvc4CommandsList.count(stringUtils::first(browsed_command, ' ')) == 1; }
        bool isTypeDeclaration() const {
            return stringUtils::split(browsed_command, ':').size() > 1
                && stringUtils::first(stringUtils::second(browsed_command, ':'), ' ') == "TYPE";
        }
        bool unsafe__isTypeDeclaration() const {
            return stringUtils::first(stringUtils::second(browsed_command, ':'), ' ') == "TYPE";
        }
    public:
        CVC4DeclBrowser(const std::string cvc4_command_string)
            : browsed_command(stringUtils::first(cvc4_command_string, ';')) { }
        bool containsDeclarations() const {
            return !isComment() && !isNonDeclarativeCommand() && !unsafe__isTypeDeclaration();
        }
        void buildDeclarationList(std::vector<std::string>& decls) {
            stringUtils::split(stringUtils::first(browsed_command, ':'), ',',
                               std::back_inserter(decls));
        }
    };

}
}

void gpid::CVC4Declarations::store(CVC4::SymbolTable* table) {
    stable = table;
}

void gpid::CVC4Declarations::collect(CVC4::Command* cmd) {
    cvc4Utils::CVC4DeclBrowser browser(cmd->toString());
    if (browser.containsDeclarations()) {
        std::vector<std::string> decls;
        browser.buildDeclarationList(decls);
        for (const std::string decl : decls) {
            nameDefs.push_back(decl);
        }
    }
}
