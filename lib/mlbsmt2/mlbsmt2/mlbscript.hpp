#ifndef MAGIC_LITERAL_BUILDER_f_SMTLIB2__SCRIPTING_TOOLS_HPP
#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__SCRIPTING_TOOLS_HPP

#include <smtlib2utils/smtlib2utils.hpp>
#include <mlbsmt2/mlbInterface.hpp>

namespace mlbsmt2 {

    enum class MlbApplicationType { Function, Equality, Comparison };

    struct MlbApplication {
        const MlbApplicationType type;
        const std::string fname;
        const bool all;
        const string_list ptypes;

        MlbApplication(const MlbApplication& o)
            : type(o.type), fname(o.fname), all(o.all), ptypes(o.ptypes) {}
        MlbApplication(MlbApplicationType t, std::string fname)
            : type(t), fname(fname), all(true) {}
        MlbApplication(MlbApplicationType t, std::string fname, const string_list& ptypes)
            : type(t), fname(fname), all(false), ptypes(ptypes) {}
    };

    class MlbScriptCHandler : public smtlib2utils::SMTl2CommandHandler {
        name_storage loadedConsts;
        function_storage loadedFuns;

        std::list<MlbApplication> applications;

        bool handleConst(const smtlib2utils::SMTl2Command& cmd);
        bool handleFun(const smtlib2utils::SMTl2Command& cmd);
        bool handleMagic(const smtlib2utils::SMTl2Command& cmd);
        bool handleApplyFun(const smtlib2utils::SMTl2Command& cmd);
        bool handleApplyEqs(const smtlib2utils::SMTl2Command& cmd);
        bool handleApplyComps(const smtlib2utils::SMTl2Command& cmd);
    public:
        MlbScriptCHandler();
    };

    class MlbScriptParser {
        smtlib2utils::SMTl2StringMemory smem;
        smtlib2utils::SMTl2CommandParser cparser;
        MlbScriptCHandler chandler;

        void _parse();
    public:
        MlbScriptParser(const std::string filename)
            : cparser(filename, smem) {}
    };

}

#endif
