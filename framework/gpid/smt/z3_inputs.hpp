#ifndef GPID_Z3_INPUT_HANDLING_HPP
#define GPID_Z3_INPUT_HANDLING_HPP

#include <gpid/smt/z3_engine.hpp>

namespace gpid {

    extern void parse_Z(const std::string& filename, z3::context& ctx, Z3Problem& pbl);

};

#endif
