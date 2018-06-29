#ifndef CVC4_API_ABDUCIBLE_GENERATION_FOR_GPID__HPP
#define CVC4_API_ABDUCIBLE_GENERATION_FOR_GPID__HPP

#include <list>
#include "cvc4-api-loaders.hpp"

namespace gpid {

    class CVC4AbducibleHandler : public AbducibleHandler {
        CVC4ProblemLoader& pbld;
        uint32_t _cpt;
        ObjectMapper<CVC4Literal>& mapper;
        std::map<uint32_t, std::list<uint32_t>>& links;
    public:
        CVC4AbducibleHandler
        (CVC4ProblemLoader& pbld, ObjectMapper<CVC4Literal>& mapper,
         std::map<uint32_t, std::list<uint32_t>>& links)
            : pbld(pbld), _cpt(0), mapper(mapper), links(links) {}
        virtual void allocate(const std::string id, size_t size) override;
        virtual void handleAbducible(std::string abd) override;

        friend class CVC4AbducibleLiteralsGenerator;
    };

    class CVC4AbducibleLiteralsGenerator {
        CVC4ProblemLoader& pbld;
        ObjectMapper<CVC4Literal> mapper;
        std::map<uint32_t, std::list<uint32_t>> links;
        CVC4AbducibleHandler handler;
    public:
        CVC4AbducibleLiteralsGenerator(CVC4ProblemLoader& pbld);

        void generate(const std::string generator);
        void load(const std::string filename);

        size_t count() const;

        inline ObjectMapper<CVC4Literal>& getMapper() { return mapper; }
        inline std::map<uint32_t, std::list<uint32_t>>& getLinks() { return links; }
    };

}

#endif
