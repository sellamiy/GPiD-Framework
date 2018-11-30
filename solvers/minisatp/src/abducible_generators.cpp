#define MINISAT_PATCHED_INTERFACE_FOR_GPID__ABDUCIBLE_GENERATORS__CPP

#include <functional>
#include <minisatp-abdgen.hpp>
#include <stdutils/collections.hpp>

using namespace gpid;
using namespace Minisat;

void MinisatAbducibleHandler::allocate(const std::string id, size_t size) {
    memoryRangeAllocation<MinisatLiteral>(id, size);
}

void MinisatAbducibleHandler::handleAbducible(const std::shared_ptr<std::string>& abd) {
    int lit_data = std::stoi(*abd);
    int lit_var = abs(lit_data)-1;
    Lit cstl = lit_data > 0 ? mkLit(lit_var) : ~mkLit(lit_var);
    memoryObjectAllocation(abducibles_memory_id, _cpt, mapper, cstl);
    // Check for literal linkage
    int lit_complement = cstl.x%2 == 0 ? cstl.x+1 : cstl.x-1;
    if (linker.find(lit_complement) == linker.end()) {
        linker[cstl.x] = _cpt;
    } else {
        links[_cpt].push_back(linker[lit_complement]);
        links[linker[lit_complement]].push_back(_cpt);
    }
    ++_cpt;
}

MinisatLiteralsGenerator::MinisatLiteralsGenerator(MinisatProblemLoader& pbld)
    : pbld(pbld), handler(pbld, mapper, links) {}

size_t MinisatLiteralsGenerator::count() const {
    return handler._cpt;
}

void MinisatLiteralsGenerator::load(const std::string filename) {
    loadAbducibles(filename, handler);
}

/* Abducible generators */

static inline size_t abdgen_minisat_all
(MinisatProblemLoader& pbld, ObjectMapper<MinisatLiteral>& mapper,
 std::map<uint32_t, std::list<uint32_t>>& links) {
    size_t size = 2*pbld.getContextManager().nVars;
    memoryRangeAllocation<MinisatLiteral>(abducibles_memory_id, size);
    for (uint32_t i = 0; i < size; i++) {
        Lit cstl;
        cstl.x = i;
        memoryObjectAllocation(abducibles_memory_id, i, mapper, cstl);
        links[i].push_back(i%2 == 0 ? i+1 : i-1);
    }
    return size;
}

using AbdgenFunctionT = std::function<size_t(MinisatProblemLoader&, ObjectMapper<MinisatLiteral>&,
                                             std::map<uint32_t, std::list<uint32_t>>&)>;
static std::map<std::string, AbdgenFunctionT> abg_minisat_abdgeneration_table = {
    { "all", AbdgenFunctionT(abdgen_minisat_all) },
    { "default", AbdgenFunctionT(abdgen_minisat_all) }
};

void MinisatLiteralsGenerator::generate(const std::string generator) {
    if (stdutils::inmap(abg_minisat_abdgeneration_table, generator)) {
        handler._cpt = abg_minisat_abdgeneration_table[generator](pbld, mapper, links);
    } else {
        snlog::l_fatal() << "Unknown minisat abducible generator: " << generator << snlog::l_end;
    }
}
