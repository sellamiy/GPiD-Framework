#define LIB_SMTLIB2_UTILS__SMTLIB2_COMMAND_PARSE_ENGINE_CPP

#include <sstream>

#include <snlog/snlog.hpp>
#include <smtlib2utils/SMTlib2CommandParser.hpp>

namespace smtlib2utils {

    static inline constexpr bool isSMTl2Whitespace(char c) {
        return c == '\t' || c == '\n' || c == '\r' || c == ' ' ;
    }

    static inline constexpr bool isSMTl2Parenthesis(char c) {
        return c == '(' || c == ')' ;
    }

    class SMTl2CParseEngine {

        SMTl2StringMemory& allocator;

        enum class EngineState { UNINITIALIZED, OPENED, CLOSED, COMPLETE, ERROR };

        std::string fsource;
        std::ifstream ssource;
        struct fpostracker { int line, col; } spos;

        EngineState state;

        SMTl2Command lastCommand;

        void start();

        void openSource();
        void closeSource();

        void handleError(std::string msg);

        void updatePositionTracker(char c);

        void parseComment();

        void nextCommand();

    public:
        SMTl2CParseEngine(const std::string& fsource, SMTl2StringMemory& allocator);
        ~SMTl2CParseEngine();

        constexpr bool valid() const {
            return state != EngineState::ERROR;
        }
        constexpr bool complete() const {
            return state == EngineState::COMPLETE;
        }

        friend class SMTl2CommandParser;
    };

    SMTl2CParseEngine::SMTl2CParseEngine
    (const std::string& fsource, SMTl2StringMemory& allocator)
        : allocator(allocator),
          fsource(fsource),
          spos({0,0}),
          state(EngineState::UNINITIALIZED),
          lastCommand("nope", std::shared_ptr<std::string>(nullptr))
    {}

    SMTl2CParseEngine::~SMTl2CParseEngine() {
        if (state == EngineState::OPENED) closeSource();
    }

    void SMTl2CParseEngine::start() {
        openSource();
    }

    void SMTl2CParseEngine::handleError(std::string msg) {
        std::stringstream buf;
        snlog::l_error() << "Parsing failure: "
                         << "@file:" << fsource
                         << ":" << std::to_string(spos.line)
                         << ":" << std::to_string(spos.col)
                         << " : " << msg
                         << snlog::l_end;
        if (state == EngineState::OPENED) closeSource();
        state = EngineState::ERROR;
    }

    void SMTl2CParseEngine::openSource() {
        snlog::t_internal(state != EngineState::UNINITIALIZED)
            << "Opening already opened abducible parser" << snlog::l_end;
        ssource = std::ifstream(fsource);
        if (!ssource.is_open()) handleError("Could not open source file");
        if (state != EngineState::ERROR) state = EngineState::OPENED;
    }

    void SMTl2CParseEngine::closeSource() {
        snlog::t_internal(state != EngineState::OPENED && state != EngineState::COMPLETE)
            << "Closing non opened abducible parser" << snlog::l_end;
        ssource.close();
        if (state == EngineState::OPENED || state == EngineState::COMPLETE)
            state = EngineState::CLOSED;
    }

    void SMTl2CParseEngine::nextCommand() {
        snlog::t_internal(state != EngineState::OPENED)
            << "Reading on uninitialized SMTlib2 parser" << snlog::l_end;
        std::stringstream cmdbuf;
        std::stringstream databuf;
        char c;
        uint64_t depth = 0;
        bool cwritten = false;
        bool ondata = false;
        while (ssource.get(c)) {
            updatePositionTracker(c);
            if (c == ';') parseComment();
            if (c == '(') depth++;
            if (c == ')') depth--;
            if (depth == 0 && cwritten) break;
            if (depth == 1) {
                if (!ondata && isSMTl2Whitespace(c)) {
                    ondata = true;
                    continue;
                }
                if (!ondata && !isSMTl2Parenthesis(c)) {
                    cmdbuf << c;
                    if (!cwritten) cwritten = true;
                }
                if (ondata)
                    databuf << c;
            }
            if (depth >= 2)
                databuf << c;
        }
        if (!cwritten) {
            state = EngineState::COMPLETE;
        }
        if (depth != 0) {
            state = EngineState::ERROR;
        }
        std::shared_ptr<std::string> dataptr = allocator.alloc(databuf);
        lastCommand = SMTl2Command(cmdbuf.str(), dataptr);
    }

    void SMTl2CParseEngine::parseComment() {
        char c;
        while(ssource.get(c)) {
            updatePositionTracker(c);
            if (c == '\n') break;
        }
    }

    void SMTl2CParseEngine::updatePositionTracker(char c) {
        if (c == '\n') { spos.line++; spos.col = 0; }
        else { spos.col++; }
    }

    bool SMTl2CommandHandler::handle(const SMTl2Command& cmd) {
        if (handlers.find(cmd.getName()) != handlers.end()) {
            return handlers[cmd.getName()](cmd);
        } else {
            snlog::l_error() << "Unknown command: " << cmd.getName() << snlog::l_end;
            return false;
        }
    }

    SMTl2CommandParser::SMTl2CommandParser(const std::string& filename, SMTl2StringMemory& allocator)
        : engine(new SMTl2CParseEngine(filename, allocator)) {}
    SMTl2CommandParser::~SMTl2CommandParser() {}

    void SMTl2CommandParser::initialize() {
        engine->start();
    }

    void SMTl2CommandParser::parse(SMTl2CommandHandler& handler) {
        bool start = true;
        while (valid() && !complete()) {
            if (start) {
                start = false;
            } else {
                handler.handle(engine->lastCommand);
            }
            engine->nextCommand();
        }
    }

    bool SMTl2CommandParser::complete() const {
        return engine->complete();
    }
    bool SMTl2CommandParser::valid() const {
        return engine->valid();
    }

}
