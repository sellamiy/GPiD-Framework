#ifndef MINISAT_PATCHED_ABDUCIBLE_GENERATION_FOR_GPID__HPP
#define MINISAT_PATCHED_ABDUCIBLE_GENERATION_FOR_GPID__HPP

#include <map>
#include <list>
#include <abdulot/core/memory.hpp>
#include <abdulot/utils/abducibles-utils.hpp>
#include "minisatp-loaders.hpp"

class MinisatAbducibleHandler : public abdulot::AbducibleHandler {
    // MinisatProblemLoader& pbld;
    uint32_t _cpt;
    abdulot::ObjectMapper<MinisatLiteral>& mapper;
    std::map<int,int> linker;
    std::map<uint32_t, std::list<uint32_t>>& links;
public:
    MinisatAbducibleHandler
    (MinisatProblemLoader&, abdulot::ObjectMapper<MinisatLiteral>& mapper,
     std::map<uint32_t, std::list<uint32_t>>& links)
        : _cpt(0), mapper(mapper), links(links) {}
    virtual void allocate(const std::string id, size_t size) override;
    virtual void handleAbducible(const std::string& abd) override;

    friend class MinisatLiteralsGenerator;
};

class MinisatLiteralsGenerator {
    MinisatProblemLoader& pbld;
    abdulot::ObjectMapper<MinisatLiteral> mapper;
    std::map<uint32_t, std::list<uint32_t>> links;
    MinisatAbducibleHandler handler;
public:
    MinisatLiteralsGenerator(MinisatProblemLoader& pbld);

    void generate(const std::string generator);
    void load(const std::string filename);

    size_t count() const;

    inline abdulot::ObjectMapper<MinisatLiteral>& getMapper() { return mapper; }
    inline std::map<uint32_t, std::list<uint32_t>>& getLinks() { return links; }
};

#endif
