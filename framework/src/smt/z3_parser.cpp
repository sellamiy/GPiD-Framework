#define Z3_PARSING

#include <gpid/smt/z3_inputs.hpp>

using namespace snlog;

namespace gpid {

    extern void parse_Z(const std::string& filename, z3::context& ctx, Z3Problem& pbl) {
        pbl.setMode(Z3Problem::IOMode::IO_WRITE);
        pbl.addConstraint(ctx.parse_file(filename.c_str()));
    }

};
