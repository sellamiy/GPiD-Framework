#define Z3_PARSING

#include <gpid/smt/z3_inputs.hpp>

using namespace snlog;

namespace gpid {

    extern void parse_Z(const std::string& filename, Z3Problem& pbl) {
        pbl.setMode(Z3Problem::IOMode::IO_WRITE);
        pbl.addConstraint(pbl.getContext().parse_file(filename.c_str()));
    }

};
