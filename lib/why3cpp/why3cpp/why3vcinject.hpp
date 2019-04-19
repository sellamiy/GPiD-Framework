#ifndef LIB_WHY3CPP__VC_INJECT_HEADER
#define LIB_WHY3CPP__VC_INJECT_HEADER

#include <set>
#include <string>
#include <sstream>

namespace why3cpp {

    extern bool vcinjectable(const std::string& source_decl, const std::set<std::string>& decls);

    extern void vcinject(std::stringstream& ss,
                         const std::string& source_decl, const std::set<std::string>& decls);

}

#endif
