#define ABDULOT__UTIL__SMTLIB2_SOLVER_ABDUCIBLE_GENERATOR_CPP

#include <abdulot/saihelpers/smtlib2.hpp>

using namespace abdulot::saihelpers;

void SMTl2AbducibleHandler::allocate(const std::string id, size_t size) {
    memoryRangeAllocation<SMTl2SolverLiteral>(id, size);
}

void SMTl2AbducibleHandler::handleAbducible(const std::shared_ptr<std::string>& abd) {
    memoryObjectAllocation(abducibles_memory_id, _cpt++, mapper, abd);
}

void SMTl2SolverAbducibleGenerator::load(std::string filename) {
    loadAbducibles(filename, handler);
}

void SMTl2SolverAbducibleGenerator::generate(std::string generatorid) {
    snlog::l_warn() << "No generator available for SMTlib2 via CLI solver interface" << snlog::l_end;
    throw UnknownUtilityError("Unknown generator id: " + generatorid);
}

size_t SMTl2SolverAbducibleGenerator::count() {
    return handler._cpt;
}
