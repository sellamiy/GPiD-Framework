#define GPID_FRAMEWORK__UTIL__SMTLIB2_SOLVER_PROBLEM_LOADER_CPP

#include <abdulot/saihelpers/smtlib2.hpp>

namespace abdulot {
namespace saihelpers {

    class SMTl2PCH_ProblemLoader : public smtlib2::SMTl2CommandHandler {
        SMTl2SolverManager& ctx;

        using constraint = std::string;
        using constraint_list = std::vector<constraint>;

        constraint_list conslist;
        typename constraint_list::iterator consit;
        bool itstart = false;

        void ensure_iteration();

        bool handleAssert(const std::string& cmd, const std::string& data);
        bool handleDeclaration(const std::string& cmd, const std::string& data);
        bool handleSetting(const std::string& cmd, const std::string& data);
        bool handleNope(const std::string&, const std::string&);
        bool handleSkip(const std::string& cmd, const std::string& data);
        bool handleEcho(const std::string& cmd, const std::string& data);
        bool handleExit(const std::string&, const std::string&);
        bool handleReset(const std::string& cmd, const std::string& data);
        bool handleResetAssertions(const std::string&, const std::string&);
        bool handleGetAssertions(const std::string&, const std::string&);
        bool handleGetSetting(const std::string& cmd, const std::string& data);
    public:
        SMTl2PCH_ProblemLoader(SMTl2SolverManager& ctx) : ctx(ctx) {
            handlers["assert"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleAssert,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["check-sat"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["check-sat-assuming"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["declare-const"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["declare-datatype"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["declare-datatypes"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["declare-fun"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["declare-sort"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["define-fun"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["define-fun-rec"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["define-funs-rec"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["define-sort"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleDeclaration,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["echo"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleEcho,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["exit"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleExit,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["get-assertions"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleGetAssertions,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["get-assignment"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["get-info"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleGetSetting,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["get-model"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["get-option"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleGetSetting,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["get-proof"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["get-unsat-assumptions"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["get-unsat-core"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["get-value"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["pop"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["push"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSkip,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["reset"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleReset,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["reset-assertions"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleResetAssertions,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["set-info"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSetting,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["set-logic"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSetting,
                          this, std::placeholders::_1, std::placeholders::_2);
            handlers["set-option"] =
                std::bind(&SMTl2PCH_ProblemLoader::handleSetting,
                          this, std::placeholders::_1, std::placeholders::_2);
        }

        bool hasNext();
        constraint& next();
    };

    bool SMTl2PCH_ProblemLoader::handleAssert(const std::string&, const std::string& data) {
        conslist.push_back(data);
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleDeclaration(const std::string& cmd, const std::string& data) {
        ctx.decls.push_back(std::pair<const std::string, const std::string>(cmd,data));
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleSetting(const std::string& cmd, const std::string& data) {
        ctx.opts.push_back(std::pair<const std::string, const std::string>(cmd,data));
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleNope(const std::string&, const std::string&) {
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleSkip(const std::string& cmd, const std::string&) {
        snlog::l_warn()
            << "Unauthorized SMTlib2 command in problem file (skipped): "
            << cmd << snlog::l_end;
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleEcho(const std::string&, const std::string& data) {
        snlog::l_message() << data << snlog::l_end;
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleExit(const std::string&, const std::string&) {
        snlog::l_info() << "Instructed to exit through the problem" << snlog::l_end;
        return false;
    }

    bool SMTl2PCH_ProblemLoader::handleReset(const std::string& cmd, const std::string& data) {
        handleResetAssertions(cmd, data);
        ctx.opts.clear();
        ctx.decls.clear();
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleResetAssertions(const std::string&, const std::string&) {
        conslist.clear();
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleGetAssertions(const std::string&, const std::string&) {
        for (constraint asptr : conslist) {
            snlog::l_message() << asptr << snlog::l_end;
        }
        return true;
    }

    bool SMTl2PCH_ProblemLoader::handleGetSetting(const std::string&, const std::string& data) {
        for (auto& setting : ctx.opts) {
            if (setting.second.find(data) != std::string::npos) {
                snlog::l_message() << setting.second << snlog::l_end;
                return true;
            }
        }
        snlog::l_warn() << "Unknown setting access required" << snlog::l_end;
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

    std::string& SMTl2PCH_ProblemLoader::next() {
        ensure_iteration();
        constraint& res = *consit;
        ++consit;
        return res;
    }

}
}

using namespace abdulot::saihelpers;

void SMTl2SolverProblemLoader::load(std::string filename, std::string language) {
    if (language != "default" && language != "smt2" && language != "SMT2") {
        snlog::l_warn() << "SMTlib2 Solver-CLI interface language input must be smt2"
                        << snlog::l_end << snlog::l_warn
                        << "Bruteforcing input file..." << snlog::l_end;
    }
    parser = std::unique_ptr<smtlib2::SMTl2CommandParser>
        (new smtlib2::SMTl2CommandParser(filename));
    parser->parse(*handler);
    if (!parser->isValid()) {
        snlog::l_fatal() << "Problem parsing error!" << snlog::l_end;
    }
}

SMTl2SolverProblemLoader::SMTl2SolverProblemLoader()
    : handler(new SMTl2PCH_ProblemLoader(ctx)) {}

void SMTl2SolverProblemLoader::prepareReader() {}

bool SMTl2SolverProblemLoader::hasConstraint() {
    auto dc_handler = static_cast<SMTl2PCH_ProblemLoader*>(handler.get());
    return dc_handler->hasNext();
}

// Local hack empty deleter for smart pointer
/* Explanation: The shared_pointer holding assertion data created by the function nextCOnstraint below
   happens to be destructed After the related ProblemLoader is, which normally means that this will
   produce a double free. We replace its deleter by this to prevent this error.
   Theoretically, it does not create any additional issues as the contraints are not used after
   the destruction of the problembuilder */
// TODO: Find a better structure for this
static auto l_del_stdstr300 = [](std::string*){};

SMTl2SolverConstraint& SMTl2SolverProblemLoader::nextConstraint() {
    auto dc_handler = static_cast<SMTl2PCH_ProblemLoader*>(handler.get());
    curr = SMTl2SolverConstraint(std::shared_ptr<std::string>(&(dc_handler->next()), l_del_stdstr300));
    return curr;
}
