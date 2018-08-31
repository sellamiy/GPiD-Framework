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
        bool handleSetting(const smtlib2utils::SMTl2Command& cmd);
        bool handleNope(const smtlib2utils::SMTl2Command&);
        bool handleSkip(const smtlib2utils::SMTl2Command& cmd);
        bool handleEcho(const smtlib2utils::SMTl2Command& cmd);
        bool handleExit(const smtlib2utils::SMTl2Command&);
        bool handleReset(const smtlib2utils::SMTl2Command& cmd);
        bool handleResetAssertions(const smtlib2utils::SMTl2Command&);
        bool handleGetAssertions(const smtlib2utils::SMTl2Command&);
        bool handleGetSetting(const smtlib2utils::SMTl2Command& cmd);
    public:
        SMTl2PCH_ProblemLoader(SMTl2SolverManager& ctx) : ctx(ctx) {
            handlers["assert"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleAssert,
                          this, std::placeholders::_1);
            handlers["check-sat"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["check-sat-assuming"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["declare-const"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["declare-datatype"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["declare-datatypes"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["declare-fun"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["declare-sort"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["define-fun"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["define-fun-rec"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["define-funs-rec"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["define-sort"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1);
            handlers["echo"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleEcho,
                          this, std::placeholders::_1);
            handlers["exit"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleExit,
                          this, std::placeholders::_1);
            handlers["get-assertions"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleGetAssertions,
                          this, std::placeholders::_1);
            handlers["get-assignment"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["get-info"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleGetSetting,
                          this, std::placeholders::_1);
            handlers["get-model"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["get-option"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleGetSetting,
                          this, std::placeholders::_1);
            handlers["get-proof"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["get-unsat-assumptions"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["get-unsat-core"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["get-value"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["pop"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["push"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1);
            handlers["reset"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleReset,
                          this, std::placeholders::_1);
            handlers["reset-assertions"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleResetAssertions,
                          this, std::placeholders::_1);
            handlers["set-info"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSetting,
                          this, std::placeholders::_1);
            handlers["set-logic"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSetting,
                          this, std::placeholders::_1);
            handlers["set-option"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSetting,
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

    bool SMTl2PCH_ProblemLoader::handleSetting(const smtlib2utils::SMTl2Command& cmd) {
        ctx.opts.push_back(cmd);
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleNope(const smtlib2utils::SMTl2Command&) {
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleSkip(const smtlib2utils::SMTl2Command& cmd) {
        snlog::l_warn("Unauthorized SMTlib2 command in problem file (skipped): " + cmd.getName());
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleEcho(const smtlib2utils::SMTl2Command& cmd) {
        snlog::l_message(cmd.getData());
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleExit(const smtlib2utils::SMTl2Command&) {
        snlog::l_info("Instructed to exit through the problem");
        return false;
    }

    bool SMTl2PCH_ProblemLoader::handleReset(const smtlib2utils::SMTl2Command& cmd) {
        handleResetAssertions(cmd);
        ctx.opts.clear();
        ctx.decls.clear();
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleResetAssertions(const smtlib2utils::SMTl2Command&) {
        conslist.clear();
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleGetAssertions(const smtlib2utils::SMTl2Command&) {
        for (constraint asptr : conslist) {
            snlog::l_message(*asptr);
        }
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleGetSetting(const smtlib2utils::SMTl2Command& cmd) {
        for (smtlib2utils::SMTl2Command& setting : ctx.opts) {
            if (setting.getData().find(cmd.getData()) != std::string::npos) {
                snlog::l_message(setting.getData());
                return true;
            }
        }
        snlog::l_warn("Unknown setting access required");
        return false;
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
