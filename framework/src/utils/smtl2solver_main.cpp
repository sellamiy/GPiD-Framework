#define GPID_FRAMEWORK__UTIL__SMTLIB2_SOLVER_INTERFACE_CPP

#include <cstdio>
#include <cstring>
#include <array>
#include <gpid/utils/smtlib2solver.hpp>

using namespace gpid;

using AssertionsT = std::map<uint64_t, std::list<std::shared_ptr<std::string>>>;

static inline void wsl2s_x_context
(std::ofstream& target, SMTl2SolverInterface::ContextManagerT& ctx) {
    for (smtlib2utils::SMTl2Command& cmd : ctx.opts) {
        target << cmd << std::endl;
    }
    for (smtlib2utils::SMTl2Command& cmd : ctx.decls) {
        target << cmd << std::endl;
    }
}

static inline void wsl2s_x_assertions
(std::ofstream& target, AssertionsT& assertions, uint64_t depth_limit) {
    for (uint64_t lvl = 0; lvl <= depth_limit; ++lvl) {
        for (std::shared_ptr<std::string> ptr : assertions[lvl]) {
            target << "(assert " << *ptr << ")" << std::endl;
        }
    }
}

static inline void wsl2s_x_query(std::ofstream& target) {
    target << "(check-sat)" << std::endl;
}

static inline void write_smtlib2_script
(SMTl2SolverInterface::ContextManagerT& ctx, AssertionsT& assertions,
 uint64_t depth_limit, const std::string script_file) {
    std::ofstream target;
    target.open(script_file);
    wsl2s_x_context(target, ctx);
    wsl2s_x_assertions(target, assertions, depth_limit);
    wsl2s_x_query(target);
    target.close();
}

#define BUFFER_SIZE 128

static inline std::string ess_get_result
(SMTl2SolverInterface::ContextManagerT&, const std::string solver_exec,
 const std::string script_file) {
    std::array<char, BUFFER_SIZE> buffer;
    std::stringstream result;
    std::string command = solver_exec + " " + script_file;
    std::shared_ptr<FILE> pipe(popen(command.c_str(), "r"), pclose);
    if (!pipe) {
        snlog::l_error("Solver execution failure (popen)");
        return "unknown";
    }
    while (!feof(pipe.get())) {
        if (fgets(buffer.data(), 128, pipe.get()) != nullptr) {
            result << buffer.data();
        }
    }
    return result.str();
}

static inline SolverTestStatus ess_analyze
(SMTl2SolverInterface::ContextManagerT&, const std::string result) {
    if (result.find("unknown") != std::string::npos) return SolverTestStatus::UNKNOWN;
    if (result.find("unsat")   != std::string::npos) return SolverTestStatus::UNSAT;
    if (result.find("sat")     != std::string::npos) return SolverTestStatus::SAT;
    snlog::l_warn("Unanswered satisfiability query!");
    snlog::l_warn("Unsafely assuming SAT for error handling consistency reasons");
    return SolverTestStatus::SAT;
}

static inline SolverTestStatus execute_solver_script
(SMTl2SolverInterface::ContextManagerT& ctx,
 const std::string solver_exec, const std::string script_file) {
    return ess_analyze(ctx, ess_get_result(ctx, solver_exec, script_file));
}

static inline void smtlib2_check_cleanup (const std::string script_file) {
    if (remove(script_file.c_str()) != 0) {
        snlog::l_warn("Couldn't delete smtl2 cli solver interface script file");
        snlog::l_error(strerror(errno));
    }
}

SolverTestStatus SMTl2SolverInterface::check() {
    const std::string script_file = "_ssivc_gpid_temp.smt2";
    write_smtlib2_script(ctx, assertions, level, script_file);
    SolverTestStatus res = execute_solver_script(ctx, solver_exec, script_file);
    smtlib2_check_cleanup(script_file);
    return res;
}

std::string SMTl2SolverInterface::getPrintableAssertions(bool negate) {
    std::stringstream sres;
    if (negate) sres << "(not ";
    sres << "(and ";
    for (uint64_t lcpt = 0; lcpt <= level; ++lcpt) {
        for (auto ptr : assertions[lcpt]) {
            sres << *ptr;
        }
    }
    sres << ")";
    if (negate) sres << ")";
    return sres.str();
}
