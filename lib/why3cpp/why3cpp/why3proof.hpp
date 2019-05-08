#ifndef LIB_WHY3CPP__PLATFORM_PROOF_HEADER
#define LIB_WHY3CPP__PLATFORM_PROOF_HEADER

#include <list>
#include <memory>
#include <stdutils/collections.hpp>
#include <why3cpp/why3config.hpp>
#include <why3cpp/why3vcinject.hpp>

namespace why3cpp {

    using vcdata_t = bool;

    static inline constexpr bool proved(const vcdata_t& vcd) { return vcd; }

    class ProofResult {
        using strptr = std::shared_ptr<std::string>;
        using index_t = uint32_t;
        bool proven;
        std::map<index_t, strptr> smtfiles;
        std::map<index_t, vcdata_t> results;
    public:
        ProofResult(bool proven, std::map<index_t, strptr>& smtfiles, std::map<index_t, vcdata_t>& results)
            : proven(proven), smtfiles(smtfiles), results(results) {}

        inline constexpr bool isComplete() const { return proven; }

        inline const std::string& getSmtFile(index_t vc) const {
            return *(smtfiles.at(vc));
        }

        inline bool isProved(index_t vc) const { return proved(results.at(vc)); }

        inline const std::map<index_t, vcdata_t>& getResults() const { return results; }

        // TODO: Add an iterator on unprovens
    };

    extern ProofResult prove
    (const std::string& filename, const std::string& prover,
     bool inject, VCInjectionMode injectmode, size_t tlim);

    static inline ProofResult prove
    (const std::string& filename, Why3ConfiguredProver prover,
     bool inject, VCInjectionMode injectmode, size_t tlim) {
        return prove(filename, str(prover), inject, injectmode, tlim);
    }

}

#endif
