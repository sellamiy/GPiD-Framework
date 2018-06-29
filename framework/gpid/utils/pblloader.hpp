#ifndef GPID_FRAMEWORK__UTILS__PBLLOADER_HPP
#define GPID_FRAMEWORK__UTILS__PBLLOADER_HPP

#include <vector>
#include <snlog/snlog.hpp>

namespace gpid {

    template<typename DeclarationsT>
    class ProblemConstraintsLoader {
    public:
        /** \brief Enum form problem generation mode */
        enum class IOMode { READ, WRITE };
        using ContextManagerT = typename DeclarationsT::ContextManagerT;
        using ConstraintT = typename DeclarationsT::ConstraintT;
    private:
        IOMode mode = IOMode::WRITE;

        ContextManagerT& ctx;
        DeclarationsT decls;

        std::vector<ConstraintT> cons_data;
        uint32_t reading_pos = -1;

        inline void initCurrentMode();
    public:
        ProblemConstraintsLoader(ContextManagerT& ctx);
        ~ProblemConstraintsLoader();

        inline void setMode(IOMode nmode) { mode = nmode; initCurrentMode(); }
        inline ContextManagerT& getContextManager() { return ctx; }
        inline DeclarationsT& getDeclarations() { return decls; }
        inline void addConstraint(ConstraintT cons);
        inline bool hasMoreConstraints();
        inline ConstraintT nextConstraint();
    };

    /* Implementation */

    template<typename DeclarationsT>
    ProblemConstraintsLoader<DeclarationsT>::ProblemConstraintsLoader(ContextManagerT& ctx)
        : ctx(ctx), decls(ctx) {}

    template<typename DeclarationsT>
    ProblemConstraintsLoader<DeclarationsT>::~ProblemConstraintsLoader() {}

    template<typename DeclarationsT>
    inline void ProblemConstraintsLoader<DeclarationsT>::addConstraint(ConstraintT cons) {
        snlog::t_warn(mode != IOMode::WRITE, "Writing problem on reading mode");
        cons_data.push_back(cons);
        decls.collect(ctx, cons);
    }

    template<typename DeclarationsT>
    inline bool ProblemConstraintsLoader<DeclarationsT>::hasMoreConstraints() {
        snlog::t_warn(mode != IOMode::READ, "Reading problem on writing mode");
        return reading_pos < cons_data.size();
    }

    template<typename DeclarationsT>
    inline typename ProblemConstraintsLoader<DeclarationsT>::ConstraintT
    ProblemConstraintsLoader<DeclarationsT>::nextConstraint() {
        snlog::t_warn(mode != IOMode::READ, "Reading problem on writing mode");
        return cons_data[reading_pos++];
    }

    template<typename DeclarationsT>
    inline void ProblemConstraintsLoader<DeclarationsT>::initCurrentMode() {
        switch (mode) {
        case IOMode::READ:
            reading_pos = 0;
            break;
        case IOMode::WRITE:
            reading_pos = -1;
            break;
        default:
            // TODO: Raise Error
            snlog::l_internal("Problem loader ended in an Unknown state!");
            break;
        }
    }

};

#endif
