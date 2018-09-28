#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__INTERFACE_CPP

#include <snlog/snlog.hpp>
#include <smtlib2utils/smtlib2utils.hpp>
#include <mlbsmt2/mlbconfig.hpp>
#include <mlbsmt2/mlbInterface.hpp>

using strptr = std::shared_ptr<std::string>;

namespace mlbsmt2 {

    class MagicParsingHandler : public smtlib2utils::SMTl2CommandHandler {

        std::list<strptr> usage;
        std::list<strptr> context;
        std::list<strptr> funs;
        std::list<strptr> sorts;
        std::list<strptr> consts;

        inline bool ignore(const smtlib2utils::SMTl2Command&) { return true; }
        bool storeAsUsage(const smtlib2utils::SMTl2Command& cmd);
        bool storeContextData(const smtlib2utils::SMTl2Command& cmd);
        bool storeFunDeclaration(const smtlib2utils::SMTl2Command& cmd);
        bool storeSortDeclaration(const smtlib2utils::SMTl2Command& cmd);
        bool storeConstDeclaration(const smtlib2utils::SMTl2Command& cmd);
    public:
        MagicParsingHandler();
    };

    class MagicLiteralData {
        MagicParsingHandler handler;
        smtlib2utils::SMTl2StringMemory smem;
    public:
        inline MagicParsingHandler& getHandler() { return handler; }
        inline smtlib2utils::SMTl2StringMemory& getMemory() { return smem; }
    };

}

using namespace mlbsmt2;

inline bool MagicParsingHandler::storeAsUsage(const smtlib2utils::SMTl2Command& cmd) {
    usage.push_back(cmd.getDataPtr());
    return true;
}

inline bool MagicParsingHandler::storeContextData(const smtlib2utils::SMTl2Command& cmd) {
    context.push_back(cmd.getDataPtr());
    return true;
}

inline bool MagicParsingHandler::storeFunDeclaration(const smtlib2utils::SMTl2Command& cmd) {
    funs.push_back(cmd.getDataPtr());
    return true;
}

inline bool MagicParsingHandler::storeSortDeclaration(const smtlib2utils::SMTl2Command& cmd) {
    sorts.push_back(cmd.getDataPtr());
    return true;
}

inline bool MagicParsingHandler::storeConstDeclaration(const smtlib2utils::SMTl2Command& cmd) {
    consts.push_back(cmd.getDataPtr());
    return true;
}

MagicParsingHandler::MagicParsingHandler() {
    handlers["assert"] = std::bind(&MagicParsingHandler::storeAsUsage, this, std::placeholders::_1);

    handlers["check-sat"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["check-sat-assuming"] =
        std::bind(&MagicParsingHandler::storeAsUsage, this, std::placeholders::_1);

    handlers["declare-const"] =
        std::bind(&MagicParsingHandler::storeConstDeclaration, this, std::placeholders::_1);
    handlers["declare-datatype"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["declare-datatypes"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["declare-fun"] =
        std::bind(&MagicParsingHandler::storeFunDeclaration, this, std::placeholders::_1);
    handlers["declare-sort"] =
        std::bind(&MagicParsingHandler::storeSortDeclaration, this, std::placeholders::_1);
    handlers["define-fun"] =
        std::bind(&MagicParsingHandler::storeFunDeclaration, this, std::placeholders::_1);
    handlers["define-fun-rec"] =
        std::bind(&MagicParsingHandler::storeFunDeclaration, this, std::placeholders::_1);
    handlers["define-funs-rec"] =
        std::bind(&MagicParsingHandler::storeFunDeclaration, this, std::placeholders::_1);
    handlers["define-sort"] =
        std::bind(&MagicParsingHandler::storeSortDeclaration, this, std::placeholders::_1);

    handlers["echo"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["exit"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);

    handlers["get-assertions"]
        = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-assignment"]
        = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-info"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-model"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-option"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-proof"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-unsat-assumptions"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-unsat-core"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-value"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);

    handlers["pop"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["push"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["reset"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["reset-assertions"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);

    handlers["set-info"] = std::bind(&MagicParsingHandler::storeContextData, this, std::placeholders::_1);
    handlers["set-logic"] = std::bind(&MagicParsingHandler::storeContextData, this, std::placeholders::_1);
    handlers["set-option"] = std::bind(&MagicParsingHandler::storeContextData, this, std::placeholders::_1);
};

/*>---------------------------------------<*/

MagicLiteralBuilder::MagicLiteralBuilder()
    : state(BuilderState::Initialized),
      data(new MagicLiteralData())
{}

MagicLiteralBuilder::~MagicLiteralBuilder() {
    data.release();
}

void MagicLiteralBuilder::loadSMTlib2File(const std::string filename) {
    smtlib2utils::SMTl2CommandParser parser(filename, data->getMemory());
    parser.initialize();
    parser.parse(data->getHandler());
}

bool MagicLiteralBuilder::exploitData(DataExploitation e) {
    snlog::l_warn("Not implemented yet %£2");
    return false;
}
