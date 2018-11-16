#define LIB_WHY3WRAP__PLATFORM_PROOF_CPP

#include <set>
#include <array>
#include <sstream>
#include <snlog/snlog.hpp>
#include <why3wrap/why3proof.hpp>
#include <why3wrap/why3proofutils.hpp>

namespace why3wrap {

    using strptr = std::shared_ptr<std::string>;
    using uintset = std::set<uint32_t>;

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
        cmd << WHY3_EXECUTABLE << " prove -a split_vc -P " << prover << " " << filename;
        return cmd.str();
    }

    static const std::string gen_extraction_command
    (const std::string& filename, const std::string& driver) {
        std::stringstream cmd;
        cmd << WHY3_EXECUTABLE << " prove -a split_vc -D " << driver << " " << filename;
        return cmd.str();
    }

    static uintset detect_unverified
    (const std::string& filename, const std::string& prover) {
        uintset res;
        SplitProofParser parser(filename, execute(gen_proof_command(filename, prover)));
        parser.parse();
        for (const SplitProofResult& r : parser.results()) {
            if (!r.isValid()) {
                res.insert(r.index);
            }
        }
        return res;
    }

    static std::list<strptr> extract_vc
    (const std::string& filename, const std::string& prover, const uintset& locations) {
        std::list<strptr> res;
        SplitProofVCParser parser(execute(gen_extraction_command(filename, driver(prover))));
        parser.parse();
        for (uint32_t idx : locations) {
            res.push_back(parser.getVC(idx));
        }
        return res;
    }

    extern ProofResult prove(const std::string& filename, const std::string& prover) {
        uintset pending = detect_unverified(filename, prover);
        if (pending.empty()) {
            ProofResult res;
            return res;
        } else {
            std::list<strptr> vcs = extract_vc(filename, prover, pending);
            for (auto it = vcs.begin(); it != vcs.end(); ++it) {
                *it = vc_sanitization(*it);
            }
            ProofResult res(vcs);
            return res;
        }
    }

}
