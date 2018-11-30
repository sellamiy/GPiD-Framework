#define LIB_WHY3CPP__PLATFORM_PROOF_CPP

#include <set>
#include <array>
#include <sstream>
#include <snlog/snlog.hpp>
#include <why3cpp/why3proof.hpp>
#include <why3cpp/why3proofutils.hpp>

namespace why3cpp {

    using strptr = std::shared_ptr<std::string>;
    using uintset = std::set<uint32_t>;
    using vcpart_t = std::pair<uint32_t, std::string>;
    using vcset_t = std::map<uint32_t, std::string>;

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
    (const std::string& filename, const std::string& prover) {
        std::stringstream cmd;
        cmd << WHY3_EXECUTABLE << " prove -a split_vc --debug print_attributes --debug transform "
            << "-P " << prover << " " << filename
            << " 2>&1";
        return cmd.str();
    }

    static const std::string gen_extraction_command
    (const std::string& filename, const std::string& driver) {
        std::stringstream cmd;
        cmd << WHY3_EXECUTABLE << " prove -a split_vc -D " << driver << " " << filename;
        return cmd.str();
    }

    static vcset_t detect_unverified
    (const std::string& filename, const std::string& prover) {
        vcset_t res;
        SplitProofParser parser(filename, execute(gen_proof_command(filename, prover)));
        parser.parse();
        if (parser.isValid()) {
            for (const SplitProofResult& r : parser.results()) {
                if (!r.isValid()) {
                    res[r.index] = r.expl;
                }
            }
        } else {
            snlog::l_internal() << "Cannot detect why3 results on empty data" << snlog::l_end;
            res[-1] = "nexpl:error";
        }
        return res;
    }

    static std::map<uint32_t, strptr> extract_vc
    (const std::string& filename, const std::string& prover, const vcset_t& locations) {
        std::map<uint32_t, strptr> res;
        SplitProofVCParser parser(execute(gen_extraction_command(filename, driver(prover))));
        parser.parse();
        for (vcpart_t vc : locations) {
            res[vc.first] = parser.getVC(vc.first);
        }
        return res;
    }

    extern ProofResult prove(const std::string& filename, const std::string& prover) {
        vcset_t pending = detect_unverified(filename, prover);
        if (pending.empty()) {
            ProofResult res;
            return res;
        } else {
            std::map<uint32_t, strptr> vcs = extract_vc(filename, prover, pending);
            for (auto it = vcs.begin(); it != vcs.end(); ++it) {
                it->second = vc_sanitization(it->second);
            }
            ProofResult res(vcs, pending);
            return res;
        }
    }

}
