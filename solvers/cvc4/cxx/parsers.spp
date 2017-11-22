#ifndef GPID_CVC4_PARSERS_SPP
#define GPID_CVC4_PARSERS_SPP

using namespace snlog;

namespace gpid {

    static void tpl_cvc4_parser(std::string filename,
                                CVC4::ExprManager& em, CVC4Problem& pbl,
                                CVC4::language::input::Language inputLanguage) {
        pbl.setMode(CVC4Problem::IOMode::IO_WRITE);
        CVC4::Options opts4;
        opts4.setInputLanguage(inputLanguage);
        CVC4::parser::ParserBuilder pb(&em, filename, opts4);
        CVC4::parser::Parser* parser = pb.build();
        CVC4::SmtEngine temp(&em);
        temp.setOption("produce-assertions", true);
        l_warn("Fixme: CVC4 Parser - safer assertions recovery handler required"); // TODO
        CVC4::Command* cmd;
        while ((cmd = parser->nextCommand())) {
            pbl.getDeclarations().collect(cmd);
            cmd->invoke(&temp);
        }
        for (CVC4::Expr expr : temp.getAssertions()) {
            pbl.addConstraint(expr);
        }
        pbl.getDeclarations().store(parser->getSymbolTable());
    }

    static void parse_CVC4_SMT2(std::string filename, CVC4::ExprManager& em, CVC4Problem& pbl) {
        tpl_cvc4_parser(filename, em, pbl, CVC4::language::input::LANG_SMTLIB_V2);
    }
    static void parse_CVC4_TPTP(std::string filename, CVC4::ExprManager& em, CVC4Problem& pbl) {
        tpl_cvc4_parser(filename, em, pbl, CVC4::language::input::LANG_TPTP);
    }
    static void parse_CVC4_CVC4(std::string filename, CVC4::ExprManager& em, CVC4Problem& pbl) {
        tpl_cvc4_parser(filename, em, pbl, CVC4::language::input::LANG_CVC4);
    }

};

#endif
