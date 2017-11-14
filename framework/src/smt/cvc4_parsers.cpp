#define CVC4_PARSING

#include <gpid/smt/cvc4_inputs.hpp>

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
            cmd->invoke(&temp);
        }
        for (CVC4::Expr expr : temp.getAssertions()) {
            pbl.addConstraint(expr);
        }
        pbl.collectDeclarations(parser->getSymbolTable());
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

    typedef void (*cvc4Parser) (std::string, CVC4::ExprManager&, CVC4Problem&);
    static std::map<std::string, cvc4Parser> cvc4Parsers =
        {
            {"smtl2",   &parse_CVC4_SMT2},
            {"tptp",    &parse_CVC4_TPTP},
            {"cvc4",    &parse_CVC4_CVC4},

            {"default", &parse_CVC4_SMT2}
        };

    extern void parse_file(std::string filename, CVC4::ExprManager& em,
                           CVC4Problem& pbl, std::string language) {
        if (cvc4Parsers.find(language) != cvc4Parsers.end()) {
            cvc4Parsers[language](filename, em, pbl);
        } else {
            snlog::l_fatal("Unknown input language for solver cvc4: " + language);
            for (std::pair<std::string, cvc4Parser> langP : cvc4Parsers) {
                snlog::l_info("   -- available: " + langP.first);
            }
        }
    }

};
