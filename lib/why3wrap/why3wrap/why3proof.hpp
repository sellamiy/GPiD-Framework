#ifndef LIB_WHY3WRAP__PLATFORM_PROOF_HEADER
#define LIB_WHY3WRAP__PLATFORM_PROOF_HEADER

#include <map>
#include <list>
#include <memory>
#include <why3wrap/why3config.hpp>

namespace why3wrap {

    class ProofResult {
        using strptr = std::shared_ptr<std::string>;
        using index_t = uint32_t;
        bool proven;
        std::map<index_t, strptr> unproven;
        std::map<index_t, std::string> explanations;
    public:
        ProofResult() : proven(true) {}
        ProofResult(std::map<index_t, strptr>& pending, std::map<index_t, std::string>& expls)
            : proven(false), unproven(pending), explanations(expls) {}

        inline constexpr bool isComplete() const { return proven; }

        inline const std::string& firstUnproven() const {
            return *(unproven.begin()->second);
        }

        inline const std::string& firstUnprovenExpl() const {
            return explanations.at(unproven.begin()->first);
        }

        inline const std::map<index_t, std::string>& getExplanations() const {
            return explanations;
        }

        // TODO: Add an iterator on unprovens
    };

    extern ProofResult prove(const std::string& filename, const std::string& prover);
    static inline ProofResult prove(const std::string& filename, Why3ConfiguredProver prover) {
        return prove(filename, str(prover));
    }

}

#endif
