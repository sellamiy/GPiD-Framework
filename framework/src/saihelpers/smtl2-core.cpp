#define GPID_FRAMEWORK__UTIL__SMTLIB2_SOLVER_INTERFACE_CPP

#include <cstdio>
#include <cstring>
#include <array>
#include <stdutils/collections.hpp>
#include <abdulot/saihelpers/smtlib2.hpp>

using namespace abdulot;
using namespace abdulot::saihelpers;

using AssertionsT = std::map<uint64_t, std::vector<std::shared_ptr<std::string>>>;

static inline void wsl2s_x_context
(std::ostream& target, SMTl2SolverInterface::ContextManagerT& ctx) {
    for (auto& p : ctx.opts) {
        target << smtlib2::SMTl2CommandWrapper(p.first, p.second) << std::endl;
    }
    for (auto& p : ctx.decls) {
        target << smtlib2::SMTl2CommandWrapper(p.first, p.second) << std::endl;
    }
}

static inline void wsl2s_x_assertions
(std::ostream& target, AssertionsT& assertions, AssertionsT& goals, uint64_t depth_limit) {
    // Writing assertions
    for (uint64_t lvl = 0; lvl <= depth_limit; ++lvl) {
        for (std::shared_ptr<std::string> ptr : assertions[lvl]) {
            target << "(assert " << *ptr << ")" << std::endl;
        }
    }
    // Writing goals
    bool goals_inited = false;
    for (uint64_t lvl = 0; lvl <= depth_limit; ++lvl) {
        for (std::shared_ptr<std::string> ptr : goals[lvl]) {
            if (!goals_inited) {
                target << "(assert (not (and ";
                goals_inited = true;
                // TODO: Initial goal negation should NOT happen here
                target << "(not " << *ptr << ")";
            } else {
                target << *ptr;
            }
        }
    }
    if (goals_inited) {
        target << ")))" << std::endl;
    }
}

static inline void wsl2s_x_query(std::ostream& target) {
    target << "(check-sat)" << std::endl;
}

static inline void write_smtlib2_script
(SMTl2SolverInterface::ContextManagerT& ctx, AssertionsT& assertions, AssertionsT& goals,
 uint64_t depth_limit, const std::string script_file) {
    std::ofstream target;
    target.open(script_file);
    wsl2s_x_context(target, ctx);
    wsl2s_x_assertions(target, assertions, goals, depth_limit);
    wsl2s_x_query(target);
    target.close();
    /*
    auto& dl = snlog::l_notifg();
    wsl2s_x_context(dl, ctx);
    wsl2s_x_assertions(dl, assertions, goals, depth_limit);
    wsl2s_x_query(dl);
    dl << snlog::l_end;
    */
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
        snlog::l_error() << "Solver execution failure (popen)" << snlog::l_end;
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
    if (result.find("timeout") != std::string::npos) return SolverTestStatus::UNKNOWN;
    if (result.find("unsat")   != std::string::npos) return SolverTestStatus::UNSAT;
    if (result.find("sat")     != std::string::npos) return SolverTestStatus::SAT;
    snlog::l_warn()
        << "Unanswered satisfiability query!" << snlog::l_end
        << snlog::l_error << result << snlog::l_end;
    return SolverTestStatus::ERROR;
}

static inline SolverTestStatus execute_solver_script
(SMTl2SolverInterface::ContextManagerT& ctx,
 const std::string solver_exec, const std::string script_file) {
    return ess_analyze(ctx, ess_get_result(ctx, solver_exec, script_file));
}

static inline void smtlib2_check_cleanup (const std::string script_file) {
    if (remove(script_file.c_str()) != 0) {
        snlog::l_warn() << "Couldn't delete smtl2 cli solver interface script file" << snlog::l_end
                        << snlog::l_error << strerror(errno) << snlog::l_end;
    }
}

static inline const std::string patch_solver_exec
(const std::string& solver_exec, const SolverInterfaceOptions& siopts,
 const SMTl2SolverInterface::TimeoutData& tdata, bool allow_float_to) {
    if (siopts.localTimeout != 0) {
        const uint64_t factorized_tlim = tdata.factor * siopts.localTimeout;
        return solver_exec + " " + tdata.cliopt + std::to_string(factorized_tlim);
    }
    if (siopts.smallLocalTimeout != 0) {
        if (allow_float_to) {
            const double factorized_tlim = tdata.factor * siopts.smallLocalTimeout;
            return solver_exec + " " + tdata.cliopt + std::to_string(factorized_tlim);
        } else {
            const uint64_t factorized_tlim = static_cast<uint64_t>(tdata.factor * siopts.smallLocalTimeout);
            return solver_exec + " " + tdata.cliopt + std::to_string(factorized_tlim);
        }
    }
    return solver_exec;
}

SolverTestStatus SMTl2SolverInterface::check() {
    write_smtlib2_script(ctx, assertions, goals, level, script_file);
    const std::string patched_solver_exec = patch_solver_exec(solver_exec, siopts, tdata, allow_float_to);
    SolverTestStatus res = execute_solver_script(ctx, patched_solver_exec, script_file);
    // snlog::l_notifg() << script_file << snlog::l_end;
    // smtlib2_check_cleanup(script_file);
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
