#define CVC4_PARSING

#include <gpid/smt/cvc4_inputs.hpp>

using namespace snlog;

namespace gpid {

    extern void parse_Cvc(const std::string& filename, CVC4::ExprManager& em, CVC4Problem& pbl) {
        pbl.setMode(CVC4Problem::IOMode::IO_WRITE);
        CVC4::Options opts4;
        opts4.setInputLanguage(CVC4::language::input::LANG_SMTLIB_V2);
        CVC4::parser::ParserBuilder pb(&em, filename, opts4);
        CVC4::parser::Parser* parser = pb.build();
        CVC4::SmtEngine temp(&em);
        temp.setOption("produce-assertions", true);
        CVC4::Command* cmd;
        while ((cmd = parser->nextCommand())) {
            cmd->invoke(&temp);
        }
        for (CVC4::Expr expr : temp.getAssertions()) {
            pbl.addConstraint(expr);
        }
    }

};
