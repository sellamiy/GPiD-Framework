#ifndef GPID_CVC4_CVC4_UTILS_SPP
#define GPID_CVC4_CVC4_UTILS_SPP

namespace gpid {
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

#endif
