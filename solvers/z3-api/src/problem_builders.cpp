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
(const std::string filename, z3::context& ctx, Z3ContraintsLoader& consld) {
    consld.setMode(Z3ContraintsLoader::IOMode::WRITE);
    consld.addConstraint(ctx.parse_file(filename.c_str()));
}

#include <map>

using LanguageldFunctionT = std::function<void(const std::string, z3::context&, Z3ContraintsLoader&)>;
static std::map<std::string, LanguageldFunctionT> pld_z3_language_table = {
    { "smt2", LanguageldFunctionT(load_z3_smt2_problem) },
    { "SMT2", LanguageldFunctionT(load_z3_smt2_problem) },
    { "default", LanguageldFunctionT(load_z3_smt2_problem) }
};

void Z3ProblemLoader::load(const std::string filename, const std::string language) {
    if (gmisc::inmap(pld_z3_language_table, language)) {
        pld_z3_language_table[language](filename, ctx, consld);
    } else {
        snlog::l_fatal("Unknown z3 input language: " + language);
    }
}
