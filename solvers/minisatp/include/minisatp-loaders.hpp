#ifndef MINISAT_PATCHED_LOADERS_FOR_GPID__HPP
#define MINISAT_PATCHED_LOADERS_FOR_GPID__HPP

#include "minisatp-context.hpp"

namespace gpid {

    class MinisatProblemLoader {
        MinisatContextManager ctx;
        MinisatDeclarations decls;

        enum class IOMode { READ, WRITE };
        IOMode mode = IOMode::WRITE;

        Minisat::vec<Minisat::Lit> cons_data;
        Minisat::vec<int> cons_sep;
        Minisat::vec<int> read_session_seps;
        Minisat::vec<Minisat::Lit> read_session_data;
        Minisat::vec<Minisat::Lit> read_local_data;

        void setMode(IOMode nmode);
        void initCurrentMode();

        void goToNextConstraint();
    public:
        MinisatProblemLoader();

        void load(const std::string filename, const std::string language);

        void prepareReader();
        bool hasConstraint();
        Minisat::vec<Minisat::Lit>& nextConstraint();
        void addConstraint(Minisat::vec<Minisat::Lit>& ps);

        inline MinisatContextManager& getContextManager() { return ctx; }
        inline MinisatDeclarations& getDeclarations() { return decls; }
    };

}

#endif
