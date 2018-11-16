#define Z3_API_INTERFACE_FOR_GPID__PROBLEM_BUILDERS__CPP

#include <functional>
#include <gpid/utils/stdutils.hpp>
#include <z3-api-loaders.hpp>

using namespace gpid;

Z3ProblemLoader::Z3ProblemLoader()
    : consld(ctx)
{}

void Z3ProblemLoader::prepareReader() {
    consld.setMode(Z3ContraintsLoader::IOMode::READ);
}

bool Z3ProblemLoader::hasConstraint() {
    return consld.hasMoreConstraints();
}

typename Z3ContraintsLoader::ConstraintT Z3ProblemLoader::nextConstraint() {
    return consld.nextConstraint();
}

/* language loaders */

static void load_z3_smt2_problem
(const std::string filename, Z3ContraintsLoader& consld) {
    z3::expr cons = consld.getContextManager().parse_file(filename.c_str());
    consld.setMode(Z3ContraintsLoader::IOMode::WRITE);
    consld.addConstraint(cons);
    consld.getDeclarations().collect(cons);
}

#include <map>

using LanguageldFunctionT = std::function<void(const std::string, Z3ContraintsLoader&)>;
static std::map<std::string, LanguageldFunctionT> pld_z3_language_table = {
    { "smt2", LanguageldFunctionT(load_z3_smt2_problem) },
    { "SMT2", LanguageldFunctionT(load_z3_smt2_problem) },
    { "default", LanguageldFunctionT(load_z3_smt2_problem) }
};

void Z3ProblemLoader::load(const std::string filename, const std::string language) {
    if (gmisc::inmap(pld_z3_language_table, language)) {
        pld_z3_language_table[language](filename, consld);
    } else {
        snlog::l_fatal() << "Unknown z3 input language: " << language << snlog::l_end;
    }
}
