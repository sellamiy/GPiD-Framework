#ifndef LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_COMMAND_PARSER_HPP
#define LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_COMMAND_PARSER_HPP

#include <fstream>
#include <functional>
#include <smtlib2tools/string-memory.hpp>

namespace smtlib2 {

    class SMTl2CommandHandler {
    protected:
        using CommandHandlerT = std::function<bool(const std::string& cmd, const std::string& cmddata)>;
        std::map<const std::string, CommandHandlerT> handlers;
    public:
        bool handle(const std::string& cmd, const std::string& cmddata) const;
    };

    struct SMTl2CommandWrapper {
        const std::string& cmd; const std::string& data;
        SMTl2CommandWrapper(const std::string& cmd, const std::string& data) : cmd(cmd), data(data) {}
    };

    inline std::ostream& operator<<(std::ostream& os, const SMTl2CommandWrapper& cmd) {
        return os << '(' << cmd.cmd << ' ' << cmd.data << ')';
    }

    class SMTl2CommandParser {
        bool valid = true;
        bool complete = false;

        const std::string filename;
        const std::shared_ptr<std::string> data;
        enum class ParserMode { File, Data };
        const ParserMode mode;
    public:
        SMTl2CommandParser(const std::string& filename)
            : filename(filename), mode(ParserMode::File) {}
        SMTl2CommandParser(std::shared_ptr<std::string> data)
            : data(data), mode(ParserMode::Data) {}
        ~SMTl2CommandParser() {}

        void parse(const SMTl2CommandHandler& handler);

        inline constexpr bool isComplete() const { return complete; }
        inline constexpr bool isValid() const { return valid; }
    };

}

#endif
