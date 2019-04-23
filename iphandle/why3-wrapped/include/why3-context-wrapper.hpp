#ifndef WHY3_WHYML_IPH_FOR_GPID__CONTEXT__HPP
#define WHY3_WHYML_IPH_FOR_GPID__CONTEXT__HPP

#include <abdulot/ilinva/options.hpp>
#include "why3-constraint-wrapper.hpp"
#include "why3-content-wrapper.hpp"

class Why3_Prop_Ctx {
    const std::string pfile;
    const std::vector<Why3_Constraint>& literals;
    const std::vector<std::string>& candidate;
    const why3cpp::Why3ConvertMap& cmap;
    const std::map<std::string, std::string>& translations;

    const size_t propid;
    const std::string solverid;
    const std::string tlim;
    const bool pinject;

    std::shared_ptr<Why3_Template> sourceCopy;
public:
    Why3_Prop_Ctx(const std::string& pfile, const std::vector<Why3_Constraint>& literals,
                   const std::vector<std::string>& candidate, const why3cpp::Why3ConvertMap& cmap,
                   const std::map<std::string, std::string>& translations, size_t propid,
                   const std::string& solverid, bool pinject, const std::string& tlim,
                   const std::shared_ptr<Why3_Template>& source)
        : pfile(pfile), literals(literals), candidate(candidate),
          cmap(cmap), translations(translations), propid(propid),
          solverid(solverid), tlim(tlim), pinject(pinject),
          sourceCopy(source) {}
    Why3_Prop_Ctx(const Why3_Prop_Ctx& o)
        : pfile(o.pfile), literals(o.literals), candidate(o.candidate),
          cmap(o.cmap), translations(o.translations), propid(o.propid),
          solverid(o.solverid), tlim(o.tlim), pinject(o.pinject),
          sourceCopy(o.sourceCopy) {}

    inline const std::string& getProblemFile() const { return pfile; }
    inline const std::vector<Why3_Constraint>& getLiterals() const { return literals; }
    inline const why3cpp::Why3ConvertMap& getCMap() const { return cmap; }
    inline const std::vector<std::string>& getCandidate() const { return candidate; }
    inline const std::map<std::string, std::string>& getTranslationMap() const { return translations; }
    inline constexpr size_t getPropertyIdentifier() const { return propid; }
    inline const std::string& getWhy3Solver() const { return solverid; }
    inline const std::string& getTlim() const { return tlim; }
    inline constexpr bool performInjections() const { return pinject; }

    inline Why3_Template& accessSourceCopy() { return *sourceCopy; }

    const Why3_Constraint getCandidateConstraint();
    const std::vector<Why3_Constraint> getCandidateConstraintDSplit();
};

#endif