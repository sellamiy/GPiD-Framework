#ifndef GPID_TRUESOLVER_SOLVER_SRC_SPP
#define GPID_TRUESOLVER_SOLVER_SRC_SPP

namespace gpid {

    class ts__solvInternal {
    public:
        std::vector<ts__hy> sst_int;
        ts__solv::ModelT    sst_mdl;
    };

    ts__solv::ts__solv() : solvers(new ts__solvInternal()) { }
    ts__solv::~ts__solv() { }

    void             ts__solv::setProblem         (ts__pbl&)          { }
    void             ts__solv::start              ()                  { }
    void             ts__solv::addHypothesis      (ts__hy&, uint32_t) { }
    void             ts__solv::removeHypotheses   (uint32_t)          { }
    void             ts__solv::printActiveNegation()                  { }
    void             ts__solv::storeActive        ()                  { }
    SolverTestStatus ts__solv::testHypotheses     (uint32_t)          { return SOLVER_UNSAT; }
    SolverTestStatus ts__solv::checkConsistency   (uint32_t)          { return SOLVER_SAT; }
    ts__mdl&         ts__solv::recoverModel       ()                  { return solvers->sst_mdl; }
    bool             ts__solv::storageSubsumed    (ts__hy&, uint32_t) { return false; }
    bool             ts__solv::isConsequence      (ts__hy&, uint32_t) { return false; }
    const std::string ts__solv::hypothesesAsString() const            { return ""; }

}

#endif
