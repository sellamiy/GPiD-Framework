#define CVC4_API_INTERFACE_FOR_GPID__PROBLEM_BUILDERS__CPP

#include <functional>
#include <cvc4-api-loaders.hpp>
#include <stdutils/collections.hpp>

CVC4ProblemLoader::CVC4ProblemLoader()
    : consld(ctx)
{}

void CVC4ProblemLoader::prepareReader() {
    consld.setMode(CVC4ContraintsLoader::IOMode::READ);
}

bool CVC4ProblemLoader::hasConstraint() {
    return consld.hasMoreConstraints();
}

typename CVC4ContraintsLoader::ConstraintT CVC4ProblemLoader::nextConstraint() {
    return consld.nextConstraint();
}

/* language loaders */

static void tpl_cvc4_parser
(std::string filename, CVC4ContraintsLoader& consld,
 CVC4::language::input::Language inputLanguage) {
    CVC4::ExprManager& em = consld.getContextManager();
    consld.setMode(CVC4ContraintsLoader::IOMode::WRITE);
    CVC4::Options opts4;
    opts4.setInputLanguage(inputLanguage);
    CVC4::parser::ParserBuilder pb(&em, filename, opts4);
    CVC4::parser::Parser* parser = pb.build();
    CVC4::SmtEngine temp(&em);
    temp.setOption("produce-assertions", true);
    snlog::l_warn() << "Fixme: CVC4 Parser - safer assertions recovery handler required"
                    << snlog::l_end; // TODO
    CVC4::Command* cmd;
    while ((cmd = parser->nextCommand())) {
        consld.getDeclarations().collect(cmd);
        cmd->invoke(&temp);
    }
    for (CVC4::Expr expr : temp.getAssertions()) {
        consld.addConstraint(expr);
    }
    consld.getDeclarations().store(parser->getSymbolTable());
}

static void tpl_load_CVC4_SMT2
(std::string filename, CVC4ContraintsLoader& consld) {
    tpl_cvc4_parser(filename, consld, CVC4::language::input::LANG_SMTLIB_V2);
}
static void tpl_load_CVC4_TPTP
(std::string filename, CVC4ContraintsLoader& consld) {
    tpl_cvc4_parser(filename, consld, CVC4::language::input::LANG_TPTP);
}
static void tpl_load_CVC4_CVC4
(std::string filename, CVC4ContraintsLoader& consld) {
    tpl_cvc4_parser(filename, consld, CVC4::language::input::LANG_CVC4);
}

#include <map>

using LanguageldFunctionT = std::function<void(const std::string, CVC4ContraintsLoader&)>;
static std::map<std::string, LanguageldFunctionT> pld_cvc4_language_table = {
    { "smt2", LanguageldFunctionT(tpl_load_CVC4_SMT2) },
    { "SMT2", LanguageldFunctionT(tpl_load_CVC4_SMT2) },
    { "tptp", LanguageldFunctionT(tpl_load_CVC4_TPTP) },
    { "TPTP", LanguageldFunctionT(tpl_load_CVC4_TPTP) },
    { "cvc4", LanguageldFunctionT(tpl_load_CVC4_CVC4) },
    { "CVC4", LanguageldFunctionT(tpl_load_CVC4_CVC4) },
    { "default", LanguageldFunctionT(tpl_load_CVC4_SMT2) }
};

void CVC4ProblemLoader::load(const std::string filename, const std::string language) {
    if (stdutils::inmap(pld_cvc4_language_table, language)) {
        pld_cvc4_language_table[language](filename, consld);
    } else {
        snlog::l_fatal() << "Unknown cvc4 input language: " << language << snlog::l_end;
    }
}
