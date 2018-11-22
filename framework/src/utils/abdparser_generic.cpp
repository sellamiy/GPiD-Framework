#define GPID_FRAMEWORK__UTIL__ABDPARSER_GENERIC_CPP

#include <snlog/snlog.hpp>
#include <gpid/core/errors.hpp>
#include <gpid/utils/abdparser.hpp>

using namespace snlog;
using namespace gpid;

/* Command handlers utils */

AbducibleParserCommandHandler::AbducibleParserCommandHandler() {
    handlers["size"] =
        std::bind(&AbducibleParserCommandHandler::handleSize,
                  this, std::placeholders::_1);
    handlers["autosize"] =
        std::bind(&AbducibleParserCommandHandler::handleSize,
                  this, std::placeholders::_1);
    handlers["abduce"] =
        std::bind(&AbducibleParserCommandHandler::handleAbducible,
                  this, std::placeholders::_1);
    handlers["abducible"] =
        std::bind(&AbducibleParserCommandHandler::handleAbducible,
                  this, std::placeholders::_1);
}

bool AbducibleParserCommandHandler::handleNothing(const smtlib2utils::SMTl2Command&)
{ return true; }

bool AbducibleParserCommandHandler::handleSize(const smtlib2utils::SMTl2Command& cmd) {
    if (cmd.getData() == "auto") {
        return auto_size = true; // p.n.: assignment required
    } else {
        size = std::stoi(cmd.getData());
        return size > 0;
    }
}

bool AbducibleParserCommandHandler::handleAbducible(const smtlib2utils::SMTl2Command& cmd) {
    abddata.push_back(cmd.getDataPtr());
    return true;
}

uint32_t AbducibleParserCommandHandler::getSize() {
    return auto_size ? abddata.size() : size;
}

const std::shared_ptr<std::string>& AbducibleParserCommandHandler::nextAbducible() {
    if (!it_init) {
        abdit = abddata.begin();
        it_init = true;
    }
    if (abdit == abddata.end()) {
        snlog::l_info()
            << "The following may be triggered by wrong size information in abducible file"
            << snlog::l_end
            << snlog::l_info
            << "The following may be an internal error"
            << snlog::l_end;
        throw IllegalAccessError("No more abducible literal");
    }
    const std::shared_ptr<std::string>& res = *abdit;
    ++abdit;
    return res;
}

/* Parser engine utils */

AbducibleParser::AbducibleParser(std::string filename)
    : cparser(filename, smem)
{}

void AbducibleParser::init() {
    cparser.initialize();
}

bool AbducibleParser::isValid() {
    return cparser.valid();
}

uint32_t AbducibleParser::getAbducibleCount() {
    if (!cparser.complete()) {
        cparser.parse(chandler);
    }
    return chandler.getSize();
}

const std::shared_ptr<std::string>& AbducibleParser::nextAbducible() {
    if (!cparser.complete()) {
        cparser.parse(chandler);
    }
    return chandler.nextAbducible();
}

