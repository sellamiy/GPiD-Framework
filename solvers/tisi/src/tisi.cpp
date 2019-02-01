#define TISI_W_DOC_FOR_GPID__CPP

#include <tisi.hpp>

using namespace gpid;
using namespace abdulot;

static TisiManager dummyManager;
static TisiConstraint dummyConstraint;
static TisiModel dummyModel;
static ObjectMapper<TisiLiteral> dummyMapper;
static std::map<typename TisiGenerator::index_t,
                std::list<typename TisiGenerator::index_t>> dummyLinks;

std::string TisiLiteral::str() { return "^_^"; }

bool TisiModel::implies(TisiLiteral&) const { return false; }

TisiManager& TisiProblemLoader::getContextManager() { return dummyManager; }
TisiManager& TisiInterface::getContextManager() { return dummyManager; }
TisiModel& TisiInterface::getModel() { return dummyModel; }

void TisiProblemLoader::load(std::string filename, std::string language) {
    std::cerr << "This should load the file " << filename
              << " with the following input language handler: " << language
              << std::endl;
}

void TisiProblemLoader::prepareReader() {}

bool TisiProblemLoader::hasConstraint() { return false; }

TisiConstraint& TisiProblemLoader::nextConstraint() { return dummyConstraint; }

TisiGenerator::TisiGenerator(TisiProblemLoader&) {}
TisiInterface::TisiInterface(TisiManager&, const SolverInterfaceOptions&) {}

void TisiGenerator::load(std::string filename) {
    std::cerr << "This should load abducible literals from " << filename
              << std::endl;
}

void TisiGenerator::generate(std::string generatorid) {
    std::cerr << "This should generate abducible using the " << generatorid
              << " method" << std::endl;
}

size_t TisiGenerator::count() { return 0; }

ObjectMapper<TisiLiteral>& TisiGenerator::getMapper() { return dummyMapper; }

std::map<typename TisiGenerator::index_t, std::list<typename TisiGenerator::index_t>>&
TisiGenerator::getLinks() { return dummyLinks; }

void TisiInterface::addConstraint(TisiConstraint&) {}

void TisiInterface::addLiteral(LiteralT&, bool) {}
void TisiInterface::clearUnsafeClauses() {}

void TisiInterface::push() {}
void TisiInterface::pop() {}

SolverTestStatus TisiInterface::check() { return SolverTestStatus::UNSAT; }

std::string TisiInterface::getPrintableAssertions(bool) { return "O_0"; }
