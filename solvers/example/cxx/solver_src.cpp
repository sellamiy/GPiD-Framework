#ifndef GPID_TRUESOLVER_SOLVER_SRC_SPP
#define GPID_TRUESOLVER_SOLVER_SRC_SPP

namespace gpid {

    class ts__solvInternal {
    public:
        std::vector<ts__lit> sst_int;
        ts__solvEngine::ModelT    sst_mdl;
    };

    ts__solvInterface::ts__solvInterface(ts__ctxm& ctxm) : AbstractSolverInterface(ctxm) { }

    ts__solvEngine::ts__solvEngine()  { }
    ts__solvEngine::~ts__solvEngine() { }

    void ts__solvEngine::printInfos()         { }
    void ts__solvEngine::setProblem(ts__pbl&) { }
    void ts__solvEngine::start     ()         { }

    void              ts__solvInterface::push                  ()         { }
    void              ts__solvInterface::pop                   ()         { }
    void              ts__solvInterface::printAssertions       (bool)     { }
    const std::string ts__solvInterface::getPrintableAssertions(bool)     { return ""; }
    void              ts__solvInterface::addLiteral            (ts__lit&, bool) { }
    void              ts__solvInterface::addClause             (HypothesisT&, LiteralMapper<LiteralT>&, bool) { }
    SolverTestStatus  ts__solvInterface::check                 () { return SolverTestStatus::UNKNOWN; }
    ts__mdl&          ts__solvInterface::getModel              () { return _internal->sst_mdl; }

    void              ts__solvInterface::clearUnsafeClauses    () { }

    std::ostream& operator<<(std::ostream& out, const LiteralHypothesisPrinter<ts__lit>&)
    { return out << "A True Solver does not print an implicate!"; }

}

#endif
