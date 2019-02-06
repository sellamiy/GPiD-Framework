#define GPID_FRAMEWORK__UTIL__ABDPARSER_GENERIC_CPP

#include <snlog/snlog.hpp>
#include <abdulot/core/errors.hpp>
#include <abdulot/utils/abducibles-core.hpp>

using namespace snlog;
using namespace abdulot;

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
    handlers["reference"] =
        std::bind(&AbducibleParserCommandHandler::handleReference,
                  this, std::placeholders::_1);
    handlers["ref"] =
        std::bind(&AbducibleParserCommandHandler::handleReference,
                  this, std::placeholders::_1);
}

bool AbducibleParserCommandHandler::handleNothing(const smtlib2::SMTl2Command&)
{ return true; }

bool AbducibleParserCommandHandler::handleSize(const smtlib2::SMTl2Command& cmd) {
    if (cmd.getData() == "auto") {
        return auto_size = true; // p.n.: assignment required
    } else {
        size = std::stoi(cmd.getData());
        return size > 0;
    }
}

bool AbducibleParserCommandHandler::handleRsize(const smtlib2::SMTl2Command& cmd) {
    if (cmd.getData() == "auto") {
        return auto_size = true; // p.n.: assignment required
    } else {
        rsize = std::stoi(cmd.getData());
        return true;
    }
}

bool AbducibleParserCommandHandler::handleAbducible(const smtlib2::SMTl2Command& cmd) {
    abddata.push_back(cmd.getDataPtr());
    return true;
}

bool AbducibleParserCommandHandler::handleReference(const smtlib2::SMTl2Command& cmd) {
    refdata.push_back(cmd.getDataPtr());
    return true;
}

uint32_t AbducibleParserCommandHandler::getSize() {
    return auto_size ? abddata.size() : size;
}

uint32_t AbducibleParserCommandHandler::getRefCount() {
    return auto_size ? refdata.size() : rsize;
}

const std::shared_ptr<std::string>& AbducibleParserCommandHandler::nextAbducible() {
    if (!ait_init) {
        abdit = abddata.begin();
        ait_init = true;
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

const std::shared_ptr<std::string>& AbducibleParserCommandHandler::nextReference() {
    if (!rit_init) {
        refit = refdata.begin();
        rit_init = true;
    }
    if (refit == refdata.end()) {
        snlog::l_info()
            << "The following may be triggered by wrong size information in abducible file"
            << snlog::l_end
            << snlog::l_info
            << "The following may be an internal error"
            << snlog::l_end;
        throw IllegalAccessError("No more reference literal");
    }
    const std::shared_ptr<std::string>& res = *refit;
    ++refit;
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

uint32_t AbducibleParser::getReferenceCount() {
    if (!cparser.complete()) {
        cparser.parse(chandler);
    }
    return chandler.getRefCount();
}

const std::shared_ptr<std::string>& AbducibleParser::nextAbducible() {
    if (!cparser.complete()) {
        cparser.parse(chandler);
    }
    return chandler.nextAbducible();
}

const std::shared_ptr<std::string>& AbducibleParser::nextReference() {
    if (!cparser.complete()) {
        cparser.parse(chandler);
    }
    return chandler.nextReference();
}
