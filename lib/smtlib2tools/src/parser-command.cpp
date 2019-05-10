#define LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_COMMAND_PARSE_ENGINE_CPP

#include <snlog/snlog.hpp>
#include <stdutils/collections.hpp>
#include <stdutils/strings.hpp>
#include <lisptp/lisptp.hpp>
#include <smtlib2tools/parser-command.hpp>

using namespace smtlib2;
using namespace lisptp;

class Smt2CommandParserHandler {
    const SMTl2CommandHandler& handler;
    bool _visit(const LispTreeNode& node);
    bool status = true;
public:
    Smt2CommandParserHandler(const SMTl2CommandHandler& handler) : handler(handler) {}
    inline bool visit(const LispTreeNode& node) { return _visit(node); }
    inline bool visit(std::shared_ptr<LispTreeNode> node) { return _visit(*node); }
};

bool Smt2CommandParserHandler::_visit(const LispTreeNode& node) {
    if (node.isCall()) {
        if (node.getValue() == global_name_wrapper || node.getValue() == "") {
            for (auto leaf: node.getLeaves())
                _visit(*leaf);
        } else {
            std::vector<std::string> lvstr(node.getLeaves().size());
            for (auto leaf: node.getLeaves())
                lvstr.push_back(leaf->str(false));
            bool _hdt = handler.handle(node.getValue(), stdutils::join(" ", lvstr));
            status = status && _hdt;
        }
    } else {
        status = false;
    }
    return status;
}

bool smtlib2::SMTl2CommandHandler::handle(const std::string& cmd, const std::string& cmddata) const {
    if (stdutils::inmap<const std::string>(handlers, cmd)) {
        return handlers.at(cmd)(cmd, cmddata);
    } else {
        snlog::l_error() << "Unknown command: " << cmd << snlog::l_end;
        return false;
    }
}

void smtlib2::SMTl2CommandParser::parse(const SMTl2CommandHandler& handler) {
    Smt2CommandParserHandler phandler(handler);
    if (mode == ParserMode::File) {
        valid = phandler.visit(lisptp::parse_file(filename));
    } else {
        valid = phandler.visit(lisptp::parse(*data));
    }
    complete = true;
}


