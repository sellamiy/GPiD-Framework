#define GPID_FRAMEWORK__UTIL__SMTLIB2_SOLVER_PROBLEM_LOADER_CPP

#include <gpid/utils/smtlib2solver.hpp>

namespace gpid {
namespace smtl2 {

    class SMTl2PCH_ProblemLoader : public smtlib2utils::SMTl2CommandHandler {
        SMTl2SolverManager& ctx;

        using constraint = std::shared_ptr<std::string>;
        using constraint_list = std::list<constraint>;

        constraint_list conslist;
        typename constraint_list::iterator consit;
        bool itstart = false;

        void ensure_iteration();

        bool handleAssert(const smtlib2utils::SMTl2Command& cmd);
        bool handleDeclaration(const smtlib2utils::SMTl2Command& cmd);
    public:
        SMTl2PCH_ProblemLoader(SMTl2SolverManager& ctx) : ctx(ctx) {
            handlers["assert"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleAssert,
                          this, std::placeholders::_1);
            handlers["declare-const"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["declare-fun"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["declare-sort"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
        }

        bool hasNext();
        constraint next();
    };

    bool SMTl2PCH_ProblemLoader::handleAssert(const smtlib2utils::SMTl2Command& cmd) {
        conslist.push_back(cmd.getDataPtr());
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleDeclaration(const smtlib2utils::SMTl2Command& cmd) {
        ctx.decls.push_back(cmd);
        return true;
    }

    void SMTl2PCH_ProblemLoader::ensure_iteration() {
        if (!itstart) {
            consit = conslist.begin();
            itstart = true;
        }
    }

    bool SMTl2PCH_ProblemLoader::hasNext() {
        ensure_iteration();
        return consit != conslist.end();
    }

    std::shared_ptr<std::string> SMTl2PCH_ProblemLoader::next() {
        ensure_iteration();
        constraint res = *consit;
        ++consit;
        return res;
    }

}
}

using namespace gpid;

void SMTl2SolverProblemLoader::load(std::string filename, std::string language) {
    if (language != "default" && language != "smt2" && language != "SMT2") {
        snlog::l_warn("SMTlib2 Solver-CLI interface language input must be smt2");
        snlog::l_warn("Bruteforcing input file...");
    }
    parser = std::unique_ptr<smtlib2utils::SMTl2CommandParser>
        (new smtlib2utils::SMTl2CommandParser(filename, ctx.memory));
    parser->initialize();
    parser->parse(*handler);
    if (!parser->valid()) {
        snlog::l_fatal("Problem parsing error!");
    }
}

SMTl2SolverProblemLoader::SMTl2SolverProblemLoader()
    : handler(new smtl2::SMTl2PCH_ProblemLoader(ctx)) {}

void SMTl2SolverProblemLoader::prepareReader() {}

bool SMTl2SolverProblemLoader::hasConstraint() {
    auto dc_handler = static_cast<smtl2::SMTl2PCH_ProblemLoader*>(handler.get());
    return dc_handler->hasNext();
}

SMTl2SolverConstraint& SMTl2SolverProblemLoader::nextConstraint() {
    auto dc_handler = static_cast<smtl2::SMTl2PCH_ProblemLoader*>(handler.get());
    curr = SMTl2SolverConstraint(dc_handler->next());
    return curr;
}
