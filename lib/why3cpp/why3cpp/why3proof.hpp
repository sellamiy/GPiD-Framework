#ifndef LIB_WHY3CPP__PLATFORM_PROOF_HEADER
#define LIB_WHY3CPP__PLATFORM_PROOF_HEADER

#include <list>
#include <memory>
#include <stdutils/collections.hpp>
#include <why3cpp/why3config.hpp>

namespace why3cpp {

    using vcdata_t = std::pair<bool, std::string>;

    static inline constexpr bool proved(const vcdata_t& vcd) { return vcd.first; }
    static inline const std::string expl(const vcdata_t& vcd) { return vcd.second; }

    class ProofResult {
        using strptr = std::shared_ptr<std::string>;
        using index_t = uint32_t;
        bool proven;
        std::map<index_t, strptr> smtfiles;
        std::map<index_t, vcdata_t> explanations;
    public:
        ProofResult(bool proven, std::map<index_t, strptr>& smtfiles, std::map<index_t, vcdata_t>& expls)
            : proven(proven), smtfiles(smtfiles), explanations(expls) {}

        inline constexpr bool isComplete() const { return proven; }

        inline const std::string& getSmtFile(index_t vc) const {
            return *(smtfiles.at(vc));
        }

        inline bool isProved(index_t vc) const { return proved(explanations.at(vc)); }

        inline const std::map<index_t, vcdata_t>& getExplanations() const {
            return explanations;
        }

        // TODO: Add an iterator on unprovens
    };

    extern ProofResult prove(const std::string& filename, const std::string& prover, bool vcreorder=true);

    static inline ProofResult
    prove(const std::string& filename, Why3ConfiguredProver prover, bool vcreorder=true) {
        return prove(filename, str(prover), vcreorder);
    }

}

#endif
