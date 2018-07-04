#ifndef TISI_W_DOC_FOR_GPID__HPP
#define TISI_W_DOC_FOR_GPID__HPP

#include <list>
#include <map>
#include <string>
#include <gpid/core/memory.hpp>
#include <gpid/core/saitypes.hpp>

namespace gpid {

    struct TisiConstraint {};

    struct TisiManager {};

    struct TisiLiteral {
        std::string str();
    };

    struct TisiModel {
        bool implies(TisiLiteral& lit) const;
    };

    class TisiProblemLoader {
    public:
        TisiManager& getContextManager();

        void load(std::string filename, std::string language);

        void prepareReader();

        bool hasConstraint();
        TisiConstraint& nextConstraint();
    };

    class TisiGenerator {
    public:
        TisiGenerator(TisiProblemLoader& loader);

        void load(std::string filename);
        void generate(std::string generatorid);

        size_t count();
        ObjectMapper<TisiLiteral>& getMapper();
        using index_t = typename ObjectMapper<TisiLiteral>::index_t;
        std::map<index_t, std::list<index_t>>& getLinks();
    };

    class TisiInterface {
    public:
        using ContextManagerT = TisiManager;
        using LiteralT = TisiLiteral;
        using ModelT = TisiModel;
        using ProblemLoaderT = TisiProblemLoader;

        TisiInterface(ContextManagerT& manager);

        ContextManagerT& getContextManager();
        ModelT& getModel();

        void addConstraint(TisiConstraint& cons);

        void addLiteral(LiteralT& lit, bool negate=false);
        template<typename ClauseIteratorGetter>
        void addClause(ClauseIteratorGetter& h, ObjectMapper<LiteralT>& mapper,
                       bool negate=false);
        void clearUnsafeClauses();

        template<typename ConjunctionIteratorGetter>
        static std::ostream& write(std::ostream& os, ContextManagerT& ctx,
                                   ConjunctionIteratorGetter& h,
                                   ObjectMapper<LiteralT>& mapper, bool negate=false);

        void push();
        void pop();
        SolverTestStatus check();

        std::string getPrintableAssertions(bool negate); // instru
    };

    template<typename ClauseIteratorGetter>
    void TisiInterface::addClause(ClauseIteratorGetter&, ObjectMapper<LiteralT>&, bool) {}

    template<typename ConjunctionIteratorGetter>
    std::ostream& TisiInterface::write
    (std::ostream& os, ContextManagerT&, ConjunctionIteratorGetter&, ObjectMapper<LiteralT>&, bool)
    { return os << "*_*"; }

}

#endif
