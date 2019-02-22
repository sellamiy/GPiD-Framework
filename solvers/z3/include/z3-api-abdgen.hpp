#ifndef Z3_API_ABDUCIBLE_GENERATION_FOR_GPID__HPP
#define Z3_API_ABDUCIBLE_GENERATION_FOR_GPID__HPP

#include <list>
#include <abdulot/core/memory.hpp>
#include <abdulot/utils/abducibles-utils.hpp>
#include "z3-api-loaders.hpp"

class Z3AbducibleHandler : public abdulot::AbducibleHandler {
    Z3ProblemLoader& pbld;
    uint32_t _cpt;
    abdulot::ObjectMapper<Z3Literal>& mapper;
    // std::map<uint32_t, std::list<uint32_t>>& links;
public:
    Z3AbducibleHandler
    (Z3ProblemLoader& pbld, abdulot::ObjectMapper<Z3Literal>& mapper,
     std::map<uint32_t, std::list<uint32_t>>&)
        : pbld(pbld), _cpt(0), mapper(mapper) {}
    virtual void allocate(const std::string id, size_t size) override;
    virtual void handleAbducible(const std::string& abd) override;

    friend class Z3AbducibleLiteralsGenerator;
};

class Z3AbducibleLiteralsGenerator {
    Z3ProblemLoader& pbld;
    abdulot::ObjectMapper<Z3Literal> mapper;
    std::map<uint32_t, std::list<uint32_t>> links;
    Z3AbducibleHandler handler;
public:
    Z3AbducibleLiteralsGenerator(Z3ProblemLoader& pbld);

    void generate(const std::string generator);
    void load(const std::string filename);

    size_t count() const;

    inline abdulot::ObjectMapper<Z3Literal>& getMapper() { return mapper; }
    inline std::map<uint32_t, std::list<uint32_t>>& getLinks() { return links; }
};

#endif
