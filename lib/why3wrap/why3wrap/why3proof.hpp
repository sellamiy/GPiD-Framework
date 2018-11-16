#ifndef LIB_WHY3WRAP__PLATFORM_PROOF_HEADER
#define LIB_WHY3WRAP__PLATFORM_PROOF_HEADER

#include <list>
#include <string>
#include <memory>
#include <why3wrap/why3config.hpp>

namespace why3wrap {

    class ProofResult {
        using strptr = std::shared_ptr<std::string>;
        bool proven;
        std::list<strptr> unproven;
    public:
        ProofResult() : proven(true) {}
        ProofResult(std::list<strptr>& pending)
            : proven(false), unproven(pending) {}

        inline constexpr bool isComplete() const { return proven; }

        inline const std::string& firstUnproven() const { return *(unproven.front()); }

        // TODO: Add an iterator on unprovens
    };

    extern ProofResult prove(const std::string& filename, const std::string& prover);
    static inline ProofResult prove(const std::string& filename, Why3ConfiguredProver prover) {
        return prove(filename, str(prover));
    }

}

#endif
