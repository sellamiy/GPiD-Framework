#define GPID_FRAMEWORK__UTIL__ABDPARSER_GENERIC_CPP

#include <snlog/snlog.hpp>
#include <gpid/util/parsers.hpp>

using namespace snlog;
using namespace gpid;

/* Additional utils */

namespace gpid {
    static inline bool aplc_ctf_isSizeCommand(std::string command) {
        return command == "size";
    }
    static inline bool aplc_ctf_isAbduceCommand(std::string command) {
        return command == "abduce" || command == "abducible";
    }
}

/* Parser engine utils */

AbducibleParser::AbducibleParser(std::string filename)
    : source(filename), pos(0, 0), status(AbdParserStatus::ABDP_0),
      abd_count(0), lastToken(AbdParserTokenType::ABDC_UNKNOWN, ""),
      lastTokenUse(false)
{}

AbducibleParser::~AbducibleParser() {
    if (status == AbdParserStatus::ABDP_OPENED) closeSource();
    if (status == AbdParserStatus::ABDP_INIT) closeSource();
}

void AbducibleParser::init() {
    t_error(status != AbdParserStatus::ABDP_0, "Abducible parser already initialized");
    openSource();
    readHeader();
    if (status != AbdParserStatus::ABDP_ERROR) status = AbdParserStatus::ABDP_INIT;
}

uint32_t AbducibleParser::getAbducibleCount() {
    t_warn(status == AbdParserStatus::ABDP_0, "Accessing uninitialized abducible parser data");
    t_warn(status == AbdParserStatus::ABDP_ERROR, "Accessing parser data after error");
    return abd_count;
}

void AbducibleParser::handleError(std::string msg) {
    std::string buf_msg = "Abducible parsing failure: ";
    buf_msg += "@file:" + source;
    buf_msg += ":" + std::to_string(pos.line) + ":" + std::to_string(pos.col);
    buf_msg += " : " + msg;
    l_error(buf_msg);
    status = AbdParserStatus::ABDP_ERROR;
}

void AbducibleParser::setOption(std::string oname, std::string ovalue) {
    if (aplc_ctf_isSizeCommand(oname)) {
        abd_count = std::stoi(ovalue);
    } else {
        handleError("Unknown abducible parser option: " + oname);
    }
}

/* File utils */

void AbducibleParser::openSource() {
    t_internal(status != AbdParserStatus::ABDP_0, "Opening already opened abducible parser");
    stream = std::ifstream(source);
    status = AbdParserStatus::ABDP_OPENED;
}

void AbducibleParser::closeSource() {
    t_internal(status == AbdParserStatus::ABDP_0, "Closing non opened abducible parser");
    t_internal(status == AbdParserStatus::ABDP_CLOSED, "Closing already closed abducible parser");
    stream.close();
    status = AbdParserStatus::ABDP_CLOSED;
}

/* Parser Utils */

void AbducibleParser::readHeader() {
    t_internal(status != AbdParserStatus::ABDP_OPENED, "Illegal abducible parser header read");
    while(true) {
        if (status != AbdParserStatus::ABDP_OPENED) break;
        AbdParserToken token = nextToken(AbdParserState::COMMAND_OUT);
        if (token.type == AbdParserTokenType::ABDC_COMMAND) {
            if (aplc_ctf_isAbduceCommand(token.content)) {
                lastToken = token;
                lastTokenUse = true;
                break;
            } else {
                readOption(token.content);
            }
        } else {
            if (token.type != AbdParserTokenType::ABDC_EOF) {
                handleError("Unexpected header token: " + token.content);
            }
            break;
        }
    }
}

void AbducibleParser::readOption(std::string oname) {
    AbdParserToken token = nextToken(AbdParserState::COMMAND_IN);
    if (token.type == AbdParserTokenType::ABDC_EXPR) {
        setOption(oname, token.content);
    } else if (token.type == AbdParserTokenType::ABDC_EOF) {
        handleError("Unexpected EOF while reading option");
    } else {
        handleError("Syntax Error: " + token.content);
    }
}

std::string AbducibleParser::nextAbducible() {
    t_error(status != AbdParserStatus::ABDP_INIT, "Illegal abducible parser read");
    std::string result = "";
    if (lastTokenUse) {
        lastTokenUse = false;
    } else {
        lastToken = nextToken(AbdParserState::COMMAND_OUT);
    }
    if (aplc_ctf_isAbduceCommand(lastToken.content)) {
        lastToken = nextToken(AbdParserState::COMMAND_IN);
        if (lastToken.type == AbdParserTokenType::ABDC_EXPR) {
            result = lastToken.content;
        } else if (lastToken.type == AbdParserTokenType::ABDC_EOF) {
            handleError("Unexpected EOF while reading abducible");
        } else {
            handleError("Syntax Error: " + lastToken.content);
        }
    } else if (lastToken.type == AbdParserTokenType::ABDC_EOF) {
        handleError("EOF");
    } else {
        handleError("Unknown abducible command: " + lastToken.content);
    }
    return result;
}

/* Lexer utils */

AbducibleParser::AbdParserToken AbducibleParser::nextToken(AbdParserState state) {
    AbdParserTokenType ded_type = AbdParserTokenType::ABDC_UNKNOWN;
    std::string buffer = "";
    char c;
    int pars = state == AbdParserState::COMMAND_IN ? 1 : 0;
    if (state == AbdParserState::COMMAND_IN) {
        while(stream.get(c)) {
            updateFilePosition(c);
            if (c == ';') skipComment();
            if (c == '(') pars++;
            if (c == ')') pars--;
            if (pars == 0) break;
            if (c == '\t' || c == '\n' || c == '\r') c = ' ';
            if (c != ' ' || buffer != "") buffer += c;
        }
        ded_type = pars == 0 ? AbdParserTokenType::ABDC_EXPR : ded_type;
    } else {
        bool cin = false;
        while(stream.get(c)) {
            updateFilePosition(c);
            if (c == ';') skipComment();
            if (c == '\t' || c == '\n' || c == '\r') c = ' ';
            if (c == ' ' && cin && buffer != "") break;
            if (c != ' ' && cin) buffer += c;
            if (c == ')') pars--;
            if (c == '(') {
                pars++;
                cin = true;
            }
        }
        ded_type = (pars == 1 && buffer != "") ? AbdParserTokenType::ABDC_COMMAND : ded_type;
    }
    if (buffer == "") ded_type = AbdParserTokenType::ABDC_EOF;
    return AbdParserToken(ded_type, buffer);
}

void AbducibleParser::skipComment() {
    char c;
    while(stream.get(c)) {
        updateFilePosition(c);
        if (c == '\n') break;
    }
}

void AbducibleParser::updateFilePosition(char c) {
    if (c == '\n') {
        pos.line++;
        pos.col = 0;
    } else
        pos.col++;
}
