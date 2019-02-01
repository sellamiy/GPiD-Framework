/**
 * \file abdulot/utils/abducibles-utils.hpp
 * \brief Additional abducible files parsing utilities.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__UTILS__ABDPARSEUTILS_HPP
#define ABDULOT__UTILS__ABDPARSEUTILS_HPP

#include <abdulot/utils/abducibles-core.hpp>

namespace abdulot {

    /** Recover the number of abducible literals in an abducible file. */
    extern uint32_t getAbducibleCount(std::string filename);

    /** Utility class for handling literals during file parsing. */
    struct AbducibleHandler {
        /** Allocates a space in memory for storing abducibles. */
        virtual void allocate(const std::string id, size_t size) = 0;
        /** Store an abducible in memory. */
        virtual void handleAbducible(const std::shared_ptr<std::string>& abd) = 0;
    };

    /** Load abducible literals from a file. */
    extern void loadAbducibles(std::string filename, AbducibleHandler& handler);

    /** Name id for storing/accessing abducible literals in memory. */
    extern const std::string abducibles_memory_id;

}

#endif
