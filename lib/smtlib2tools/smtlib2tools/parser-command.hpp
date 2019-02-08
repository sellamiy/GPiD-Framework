#ifndef LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_COMMAND_PARSER_HPP
#define LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_COMMAND_PARSER_HPP

#include <fstream>
#include <functional>
#include <smtlib2tools/string-memory.hpp>

namespace smtlib2 {

    class SMTl2Command {
        std::string name;
        std::shared_ptr<std::string> data;
    public:
        SMTl2Command(const std::string& n, const std::shared_ptr<std::string>& d)
            : name(n), data(d) {}
        SMTl2Command(const SMTl2Command& o)
            : name(o.name), data(o.data) {}

        inline std::string getName() const { return name; }
        inline std::string getData() const { return *data; }
        inline const std::shared_ptr<std::string>& getDataPtr() const { return data; }
    };

    inline std::ostream& operator<<(std::ostream& os, const SMTl2Command& cmd) {
        return os << "(" << cmd.getName() << " " << cmd.getData() << ")";
    }

    class SMTl2CommandHandler {
    protected:
        using CommandHandlerT = std::function<bool(const SMTl2Command& cmd)>;
        std::map<const std::string, CommandHandlerT> handlers;
    public:
        bool handle(const SMTl2Command& cmd);
    };

    class SMTl2CParseEngine;

    class SMTl2CommandParser {
        std::unique_ptr<SMTl2CParseEngine> engine;
    public:
        SMTl2CommandParser(const std::string& filename, StringMemory& allocator);
        SMTl2CommandParser(std::shared_ptr<std::string> data, StringMemory& allocator);
        ~SMTl2CommandParser();

        void initialize();
        void parse(SMTl2CommandHandler& handler);

        bool complete() const;
        bool valid() const;
    };

}

#endif
