#define LIB_WHY3CPP__PLATFORM_PROOF_CPP

#include <array>
#include <sstream>
#include <snlog/snlog.hpp>
#include <why3cpp/why3proof.hpp>
#include <why3cpp/why3proofutils.hpp>

namespace why3cpp {

    using strptr = std::shared_ptr<std::string>;
    using uintset = std::set<uint32_t>;
    using vcpart_t = std::pair<uint32_t, std::string>;
    using vcset_t = std::map<uint32_t, vcdata_t>;

#define BUFFER_SIZE 128
    static const strptr execute(const std::string& command) {
        std::array<char, BUFFER_SIZE> buffer;
        std::stringstream result;
        std::shared_ptr<FILE> pipe(popen(command.c_str(), "r"), pclose);
        if (!pipe) {
            snlog::l_error() << "Why3 Proof command instantiation failure (popen)" << snlog::l_end;
            return strptr(new std::string());
        }
        while (!feof(pipe.get())) {
            if (fgets(buffer.data(), 128, pipe.get()) != nullptr) {
                result << buffer.data();
            }
        }
        return strptr(new std::string(result.str()));
    }

    static const std::string gen_proof_command
    (const std::string& filename, const std::string& prover, const size_t tlim, const std::string& config) {
        std::stringstream cmd;
        cmd << WHY3_EXECUTABLE << " prove -a split_vc ";
        if (config != "" ) cmd << "-C " << config << " ";
        cmd << "--timelimit " << tlim << " "
            << "-P " << prover << " " << filename
            << " 2>&1";
        return cmd.str();
    }

    static const std::string gen_extraction_command
    (const std::string& filename, const std::string& driver, const std::string& config) {
        std::stringstream cmd;
        cmd << WHY3_EXECUTABLE << " prove -a split_vc ";
        if (config != "" ) cmd << "-C " << config << " ";
        cmd << "-D " << driver << " " << filename;
        return cmd.str();
    }

    static bool detect_unverified
    (const std::string& filename, const std::string& prover, vcset_t& res,
     const size_t tlim, const std::string& config) {
        SplitProofParser parser(filename, execute(gen_proof_command(filename, prover, tlim, config)));
        bool proofcomplete = true;
        parser.parse();
        if (parser.isValid()) {
            for (const SplitProofResult& r : parser.results()) {
                res[r.index] = vcdata_t(r.isValid());
                proofcomplete = proofcomplete && r.isValid();
            }
        } else {
            proofcomplete = false;
            snlog::l_internal() << "Cannot detect why3 results on empty data" << snlog::l_end;
            res[-1] = vcdata_t(false);
        }
        return proofcomplete;
    }

    static std::map<uint32_t, strptr> extract_vc
    (const std::string& filename, const std::string& prover,
     const vcset_t& locations, const std::string& config) {
        std::map<uint32_t, strptr> res;
        SplitProofVCParser parser(execute(gen_extraction_command(filename, driver(prover), config)));
        parser.parse();
        for (const auto& vc : locations) {
            res[vc.first] = parser.getVC(vc.first);
        }
        return res;
    }

    extern ProofResult prove
    (const std::string& filename, const std::string& prover,
     bool inject, VCInjectionMode injectmode, size_t tlim, const std::string& config) {
        vcset_t extractall;
        if (tlim == 0) tlim = 1; // TODO: This is a beurk Hack to prevent unwanted small 0 smtlim
        const bool dres = detect_unverified(filename, prover, extractall, tlim, config);
        std::map<uint32_t, strptr> vcs = extract_vc(filename, prover, extractall, config);
        for (auto it = vcs.begin(); it != vcs.end(); ++it) {
            it->second = vc_sanitization(it->second, inject, injectmode);
        }
        ProofResult res(dres, vcs, extractall);
        return res;
    }

}
