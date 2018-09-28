#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__INTERFACE_CPP

#include <snlog/snlog.hpp>
#include <smtlib2utils/smtlib2utils.hpp>
#include <mlbsmt2/mlbconfig.hpp>
#include <mlbsmt2/mlbInterface.hpp>

namespace mlbsmt2 {

    class MagicParsingHandler : public smtlib2utils::SMTl2CommandHandler {

        // bool handleSize(const smtlib2utils::SMTl2Command& cmd);
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

MagicParsingHandler::MagicParsingHandler() {
    // handlers["<*>"] = std::bind(&MagicParsingHandler::handle<*>, this, std::placeholders::_1);
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
