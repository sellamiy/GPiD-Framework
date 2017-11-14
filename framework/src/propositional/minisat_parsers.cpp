#define MINISAT_DIMACS_PARSING

#include <gpid/propositional/minisat_inputs.hpp>
#include <minisat/core/Dimacs.h>

namespace gpid {

    class Wrap_MSPbl_SolverT {
        MinisatProblem& intern;
    public:
        Wrap_MSPbl_SolverT(MinisatProblem& P) : intern(P) {}

        inline void addClause_(Minisat::vec<Minisat::Lit>& ps)
        { intern.addConstraint(ps); }

        inline int nVars()   { return intern.getVarCpt(); }
        inline void newVar() { intern.newVar(); }
    };

    static void parse_DIMACS(std::string filename, MinisatProblem& P) {
        gzFile input_stream = gzopen(filename.c_str(), "rb"); // TODO: Handle input errors
        Wrap_MSPbl_SolverT wrapper(P);
        Minisat::parse_DIMACS(input_stream, wrapper);
        gzclose(input_stream);
    }

    typedef void (*minisatParser) (std::string, MinisatProblem&);
    static std::map<std::string, minisatParser> minisatParsers =
        {
            {"dimacs",  &parse_DIMACS},

            {"default", &parse_DIMACS}
        };

    extern void parse_file(std::string filename, MinisatProblem& P, std::string language) {
        if (minisatParsers.find(language) != minisatParsers.end()) {
            minisatParsers[language](filename, P);
        } else {
            snlog::l_fatal("Unknown input language for solver minisat: " + language);
            for (std::pair<std::string, minisatParser> langP : minisatParsers) {
                snlog::l_info("   -- available: " + langP.first);
            }
        }
    }

};
