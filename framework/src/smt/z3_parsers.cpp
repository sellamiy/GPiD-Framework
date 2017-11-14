#define Z3_PARSING

#include <gpid/smt/z3_inputs.hpp>

using namespace snlog;

namespace gpid {

    static void parse_Z3_SMT2(std::string filename, Z3Problem& pbl) {
        pbl.setMode(Z3Problem::IOMode::IO_WRITE);
        pbl.addConstraint(pbl.getContext().parse_file(filename.c_str()));
    }

    typedef void (*z3Parser) (std::string, Z3Problem&);
    static std::map<std::string, z3Parser> z3Parsers =
        {
            {"smtl2",   &parse_Z3_SMT2},

            {"default", &parse_Z3_SMT2}
        };

    extern void parse_file(std::string filename, Z3Problem& pbl, std::string language) {
        if (z3Parsers.find(language) != z3Parsers.end()) {
            z3Parsers[language](filename, pbl);
        } else {
            snlog::l_fatal("Unknown input language for solver z3: " + language);
            for (std::pair<std::string, z3Parser> langP : z3Parsers) {
                snlog::l_info("   -- available: " + langP.first);
            }
        }
    }

};
