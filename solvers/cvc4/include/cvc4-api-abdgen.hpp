#ifndef CVC4_API_ABDUCIBLE_GENERATION_FOR_GPID__HPP
#define CVC4_API_ABDUCIBLE_GENERATION_FOR_GPID__HPP

#include <vector>
#include <abdulot/core/memory.hpp>
#include <abdulot/utils/abducibles-utils.hpp>
#include "cvc4-api-loaders.hpp"

class CVC4AbducibleHandler : public abdulot::AbducibleHandler {
    CVC4ProblemLoader& pbld;
    uint32_t _cpt;
    abdulot::ObjectMapper<CVC4Literal>& mapper;
    // std::map<uint32_t, std::vector<uint32_t>>& links;
public:
    CVC4AbducibleHandler
    (CVC4ProblemLoader& pbld, abdulot::ObjectMapper<CVC4Literal>& mapper,
     std::map<uint32_t, std::vector<uint32_t>>&)
        : pbld(pbld), _cpt(0), mapper(mapper) {}
    virtual void allocate(const std::string id, size_t size) override;
    virtual void handleAbducible(const std::string& abd) override;

    friend class CVC4AbducibleLiteralsGenerator;
};

class CVC4AbducibleLiteralsGenerator {
    CVC4ProblemLoader& pbld;
    abdulot::ObjectMapper<CVC4Literal> mapper;
    std::map<uint32_t, std::vector<uint32_t>> links;
    CVC4AbducibleHandler handler;
public:
    CVC4AbducibleLiteralsGenerator(CVC4ProblemLoader& pbld);

    void generate(const std::string generator);
    void load(const std::string filename);

    size_t count() const;

    inline abdulot::ObjectMapper<CVC4Literal>& getMapper() { return mapper; }
    inline std::map<uint32_t, std::vector<uint32_t>>& getLinks() { return links; }
};

#endif
