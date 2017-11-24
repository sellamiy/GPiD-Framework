#ifndef GPID_Z3_PARSERS_SPP
#define GPID_Z3_PARSERS_SPP

using namespace snlog;

namespace gpid {

    static void parse_Z3_SMT2(std::string filename, z3::context&, Z3Problem& pbl) {
        pbl.setMode(Z3Problem::IOMode::IO_WRITE);
        pbl.addConstraint(pbl.getContextManager().parse_file(filename.c_str()));
    }

};

#endif
