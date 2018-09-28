#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__INTERFACE_CPP

#include <snlog/snlog.hpp>
#include <mlbsmt2/mlbconfig.hpp>
#include <mlbsmt2/mlbInterface.hpp>

namespace mlbsmt2 {

    class MagicLiteralData {

    public:
    };

}

using namespace mlbsmt2;

/*>---------------------------------------<*/

MagicLiteralBuilder::MagicLiteralBuilder()
    : state(BuilderState::Initialized),
      data(new MagicLiteralData())
{}

MagicLiteralBuilder::~MagicLiteralBuilder() {
    data.release();
}

void MagicLiteralBuilder::loadSMTlib2File(const std::string filename) {
    snlog::l_warn("Not implemented yet %£1");
}

bool MagicLiteralBuilder::exploitData(DataExploitation e) {
    snlog::l_warn("Not implemented yet %£2");
    return false;
}
