#ifndef GPID_FRAMEWORK__LOADERS__ABDPARSEUTILS_HPP
#define GPID_FRAMEWORK__LOADERS__ABDPARSEUTILS_HPP

#include <gpid/loaders/abdparser.hpp>

namespace gpid {

    extern uint32_t getAbducibleCount(std::string filename);

    struct AbducibleHandler {
        virtual void allocate(const std::string id, size_t size) = 0;
        virtual void handleAbducible(std::string abd) = 0;
    };

    extern void loadAbducibles(std::string filename, AbducibleHandler& handler);

    extern const std::string abducibles_memory_id;

}

#endif
