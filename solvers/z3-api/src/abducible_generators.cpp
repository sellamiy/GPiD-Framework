#define Z3_API_INTERFACE_FOR_GPID__ABDUCIBLE_GENERATORS__CPP

#include <functional>
#include <gpid/utils/stdutils.hpp>
#include <z3-api-abdgen.hpp>

using namespace gpid;

void Z3AbducibleHandler::allocate(const std::string id, size_t size) {
    memoryRangeAllocation<Z3Literal>(id, size);
}

void Z3AbducibleHandler::handleAbducible(const std::shared_ptr<std::string>& abd) {
    std::string smt_assert = "(assert " + *abd + ")";
    z3::expr cstl = pbld.getContextManager().parse_string
        (smt_assert.c_str(),
         pbld.getDeclarations().getSortDecls(),
         pbld.getDeclarations().getFunDecls());
    memoryObjectAllocation(abducibles_memory_id, _cpt++, mapper, cstl);
}

Z3AbducibleLiteralsGenerator::Z3AbducibleLiteralsGenerator(Z3ProblemLoader& pbld)
    : pbld(pbld), handler(pbld, mapper, links) {}

size_t Z3AbducibleLiteralsGenerator::count() const {
    return handler._cpt;
}

void Z3AbducibleLiteralsGenerator::load(const std::string filename) {
    loadAbducibles(filename, handler);
}

/* Abducible generators */

#include <map>

static inline size_t abdgen_z3_constAllEq
(Z3ProblemLoader& pbld, ObjectMapper<Z3Literal>& mapper, std::map<uint32_t, std::list<uint32_t>>& links) {
    uint32_t l_gvr = pbld.getDeclarations().getFunDecls().size();
    size_t size = l_gvr > 1 ? l_gvr * (l_gvr - 1) : 0;
    memoryRangeAllocation<Z3Literal>(abducibles_memory_id, size);
    uint32_t vCount = pbld.getDeclarations().getFunDecls().size();
    uint32_t pos = 0;
    for (uint32_t i = 0; i < vCount; i++) {
        for (uint32_t j = i+1; j < vCount; j++) {
            z3::expr cstl_eq = pbld.getDeclarations().getFunDecls()[i]() == pbld.getDeclarations().getFunDecls()[j]();
            z3::expr cstl_neq = pbld.getDeclarations().getFunDecls()[i]() != pbld.getDeclarations().getFunDecls()[j]();
            memoryObjectAllocation(abducibles_memory_id, pos, mapper, cstl_eq);
            memoryObjectAllocation(abducibles_memory_id, pos+1, mapper, cstl_neq);
            links[pos].push_back(pos+1);
            links[pos+1].push_back(pos);
            pos += 2;
        }
    }
    return size;
}

static inline size_t abdgen_z3_constAllComp
(Z3ProblemLoader& pbld, ObjectMapper<Z3Literal>& mapper, std::map<uint32_t, std::list<uint32_t>>& links) {
    uint32_t l_gvr = pbld.getDeclarations().getFunDecls().size();
    size_t size = l_gvr > 1 ? l_gvr * (l_gvr - 1) * 2 : 0;
    memoryRangeAllocation<Z3Literal>(abducibles_memory_id, size);
    uint32_t vCount = pbld.getDeclarations().getFunDecls().size();
    uint32_t pos = 0;
    for (uint32_t i = 0; i < vCount; i++) {
        for (uint32_t j = i+1; j < vCount; j++) {
            z3::expr cstl_gt =
                pbld.getDeclarations().getFunDecls()[i]() >
                pbld.getDeclarations().getFunDecls()[j]();
            z3::expr cstl_ge =
                pbld.getDeclarations().getFunDecls()[i]() >=
                pbld.getDeclarations().getFunDecls()[j]();
            z3::expr cstl_lt =
                pbld.getDeclarations().getFunDecls()[i]() <
                pbld.getDeclarations().getFunDecls()[j]();
            z3::expr cstl_le =
                pbld.getDeclarations().getFunDecls()[i]() <=
                pbld.getDeclarations().getFunDecls()[j]();
            memoryObjectAllocation(abducibles_memory_id, pos, mapper, cstl_gt);
            memoryObjectAllocation(abducibles_memory_id, pos+1, mapper, cstl_ge);
            memoryObjectAllocation(abducibles_memory_id, pos+2, mapper, cstl_lt);
            memoryObjectAllocation(abducibles_memory_id, pos+3, mapper, cstl_le);
            links[pos].push_back(pos+1);
            links[pos].push_back(pos+2);
            links[pos].push_back(pos+3);
            links[pos+1].push_back(pos+2);
            links[pos+1].push_back(pos+3);
            links[pos+2].push_back(pos+3);
            links[pos+1].push_back(pos);
            links[pos+2].push_back(pos);
            links[pos+3].push_back(pos);
            links[pos+2].push_back(pos+1);
            links[pos+3].push_back(pos+1);
            links[pos+3].push_back(pos+2);
            pos += 4;
        }
    }
    return size;
}

using AbdgenFunctionT = std::function<size_t(Z3ProblemLoader&, ObjectMapper<Z3Literal>&,
                                             std::map<uint32_t, std::list<uint32_t>>&)>;
static std::map<std::string, AbdgenFunctionT> abg_z3_abdgeneration_table = {
    { "const-all-eq", AbdgenFunctionT(abdgen_z3_constAllEq) },
    { "const-all-comp", AbdgenFunctionT(abdgen_z3_constAllComp) },
    { "default", AbdgenFunctionT(abdgen_z3_constAllEq) }
};

void Z3AbducibleLiteralsGenerator::generate(const std::string generator) {
    if (gmisc::inmap(abg_z3_abdgeneration_table, generator)) {
        handler._cpt = abg_z3_abdgeneration_table[generator](pbld, mapper, links);
    } else {
        snlog::l_fatal() << "Unknown z3 abducible generator: " << generator << snlog::l_end;
    }
}
