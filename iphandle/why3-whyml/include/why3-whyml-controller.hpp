#ifndef WHY3_WHYML_IPH_FOR_GPID__PROBLEM_CONTROLLER__HPP
#define WHY3_WHYML_IPH_FOR_GPID__PROBLEM_CONTROLLER__HPP

#include <stack>
#include <abdulot/ilinva/iph-core.hpp>
#include "why3-whyml-source.hpp"

// Maps @block ---> < why3vc-identifier, why3property-identifier >
using block_t = std::pair<size_t, size_t>;
using blockmap_t = std::map<size_t, block_t>;

static inline size_t vc_ident(const blockmap_t& bm, size_t id) { return bm.at(id).first; }
static inline size_t prop_ident(const blockmap_t& bm, size_t id) { return bm.at(id).second; }

using blockcache_t = std::vector<std::set<block_t>>;

using stringoptionmap_t = std::map<std::string, std::string>;
using booloptionmap_t = std::map<std::string, bool>;

class W3WML_ShapeDetector {
    std::map<size_t, std::string> properties_shape;
    std::map<size_t, std::string> vc_shape;
public:
    W3WML_ShapeDetector(const W3WML_Template& sourcedata) {
        for (size_t pid : sourcedata.getPropertyIds())
            properties_shape[pid] = sourcedata.getProperty(pid).type;
    }

    bool canGenerateBlock(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const;

    block_t generateBlock(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const;

    inline bool isVCShaped() const { return vc_shape.size() > 0; }

    void detectVCShape(const why3cpp::ProofResult& pr);
};

class W3WML_ProblemController {
public:
    using blockid_t = size_t;

    static const std::string w3opt_solver;
    static const std::string w3opt_vcreorder;

    static const std::string w3opt_cmapmode;
private:
    W3WML_Template sourcedata;
    W3WML_ShapeDetector shape;

    why3cpp::Why3ConvertMap& cmap;

    blockmap_t blockmap;
    blockcache_t blockcache;
    blockid_t _gvid = 0;

    inline blockid_t newblockid() { return _gvid++; }

    std::stack<why3cpp::ProofResult> prcache;
    bool prcached = false;

    stringoptionmap_t& sopts;
    booloptionmap_t& bopts;

    std::map<blockid_t, const std::string> filecache;

    inline void pushcache() { prcached = false; }
    inline void popcache() {
        if (prcache.size() > 0)
            prcache.pop();
        prcached = prcache.size() > 0;
    }
    inline void flushcache() { prcached = false; }
    inline void cachepr(const why3cpp::ProofResult& pr) {
        if (prcached)
            prcache.pop();
        prcache.push(pr);
        prcached = true;
    }
    inline why3cpp::ProofResult& getCachedPr() { return prcache.top(); }

    inline void encacheBlockFile(blockid_t id, const std::string& filename) {
        filecache.insert(std::pair<blockid_t, const std::string>(id, filename));
    }

    why3cpp::ProofResult getWhy3Proof();
public:
    W3WML_ProblemController
    (const std::string& filename, why3cpp::Why3ConvertMap& cmap, stringoptionmap_t& sopts, booloptionmap_t& bopts)
        : sourcedata(filename), shape(sourcedata), cmap(cmap),
          sopts(sopts), bopts(bopts)
    {}

    inline const why3cpp::Why3ConvertMap& getCMap() const { return cmap; }

    inline void exportSource(const std::string& filename) const {
        sourcedata.save_to(filename, cmap);
    }

    inline void exportSource(std::ostream& out) const {
        write(out, sourcedata, cmap);
    }

    inline const std::string& getStringOption(const std::string& optname) const {
        return sopts.at(optname);
    }

    inline bool getBoolOption(const std::string& optname) const {
        return bopts.at(optname);
    }

    inline std::vector<const std::string>& getCandidateConjunction(blockid_t id) {
        auto property = prop_ident(blockmap, id);
        return sourcedata.getProperty(property).conj;
    }

    inline void strengthen(blockid_t id, W3WML_Constraint cons) {
        pushcache();
        auto property = prop_ident(blockmap, id);
        sourcedata.getProperty(property).conj.push_back(cons);
        write(snlog::l_message() << "@C[" << id << "]: ", sourcedata.getProperty(property), cmap)
            << snlog::l_end;
    }

    inline void release(blockid_t id) {
        if (id != ((blockid_t)(-1))) {
            popcache();
            auto property = prop_ident(blockmap, id);
            // Check required for first strengthening
            if (!sourcedata.getProperty(property).conj.empty()) {
                sourcedata.getProperty(property).conj.pop_back();
            }
        }
    }

    inline const std::string& getBlockFile(blockid_t id) const { return filecache.at(id); }

    abdulot::ilinva::IphState proofCheck();

    bool hasNextUnprovenBlock(size_t id);

    blockid_t selectUnprovenBlock(size_t id);

    const std::string generateAbductionProblem(blockid_t id);

};

#endif
