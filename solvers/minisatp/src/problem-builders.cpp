#define MINISAT_PATCHED_INTERFACE_FOR_GPID__PROBLEM_BUILDERS__CPP

#include <functional>
#include <minisatp-loaders.hpp>
#include <minisat/core/Dimacs.h>
#include <snlog/snlog.hpp>
#include <stdutils/collections.hpp>

MinisatProblemLoader::MinisatProblemLoader() {}

void MinisatProblemLoader::setMode(IOMode nmode) {
    mode = nmode;
    initCurrentMode();
}

void MinisatProblemLoader::initCurrentMode() {
    switch (mode) {
    case IOMode::READ:
        cons_sep.copyTo(read_session_seps);
        cons_data.copyTo(read_session_data);
        break;
    case IOMode::WRITE:
        read_session_seps.clear();
        read_session_data.clear();
        break;
    default:
        // TODO: Raise Error
        snlog::l_internal() << "Minisat problem ended in an Unknown state!" << snlog::l_end;
        break;
    }
}

void MinisatProblemLoader::addConstraint(Minisat::vec<Minisat::Lit>& ps) {
    if (mode != IOMode::WRITE) {
        // TODO: Raise Error
        snlog::l_warn() << "Writing problem on reading mode!" << snlog::l_end;
    }
    cons_sep.push(cons_data.size());
    for (int i = 0; i < ps.size(); i++)
        cons_data.push(ps[i]);
}

void MinisatProblemLoader::goToNextConstraint() {
    read_local_data.clear();
    while (read_session_data.size() > read_session_seps.last()) {
        read_local_data.push(read_session_data.last());
        read_session_data.pop();
    }
    read_session_seps.pop();
}

bool MinisatProblemLoader::hasConstraint() {
    if (mode != IOMode::READ) {
        // TODO: Raise Error
        snlog::l_warn() << "Reading problem on writing mode!" << snlog::l_end;
    }
    return read_session_seps.size() > 0;
}

Minisat::vec<Minisat::Lit>& MinisatProblemLoader::nextConstraint() {
    if (mode != IOMode::READ) {
        // TODO: Raise Error
        snlog::l_warn() << "Reading problem on writing mode!" << snlog::l_end;
    }
    goToNextConstraint();
    return read_local_data;
}

void MinisatProblemLoader::prepareReader() {
    setMode(IOMode::READ);
}

/* language loaders */

class Wrap_MSPbl_SolverT {
    MinisatProblemLoader& intern;
public:
    Wrap_MSPbl_SolverT(MinisatProblemLoader& P) : intern(P) {}

    inline void addClause_(Minisat::vec<Minisat::Lit>& ps)
    { intern.addConstraint(ps); }

    inline int nVars()   { return intern.getContextManager().nVars; }
    inline void newVar() { intern.getContextManager().newVar(); }
};

static void load_DIMACS_problem(std::string filename, MinisatProblemLoader& P) {
    gzFile input_stream = gzopen(filename.c_str(), "rb"); // TODO: Handle input errors
    Wrap_MSPbl_SolverT wrapper(P);
    Minisat::parse_DIMACS(input_stream, wrapper);
    gzclose(input_stream);
}

#include <map>

using LanguageldFunctionT = std::function<void(const std::string, MinisatProblemLoader&)>;
static std::map<std::string, LanguageldFunctionT> pld_minisat_language_table = {
    { "dimacs", LanguageldFunctionT(load_DIMACS_problem) },
    { "DIMACS", LanguageldFunctionT(load_DIMACS_problem) },
    { "default", LanguageldFunctionT(load_DIMACS_problem) }
};

void MinisatProblemLoader::load(const std::string filename, const std::string language) {
    if (stdutils::inmap(pld_minisat_language_table, language)) {
        pld_minisat_language_table[language](filename, *this);
    } else {
        snlog::l_fatal() << "Unknown minisat input language: " << language << snlog::l_end;
    }
}
