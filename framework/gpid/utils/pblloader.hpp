/**
 * \file gpid/utils/pblloader.hpp
 * \brief GPiD Problem loader generic template.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__UTILS__PBLLOADER_HPP
#define GPID_FRAMEWORK__UTILS__PBLLOADER_HPP

#include <vector>
#include <snlog/snlog.hpp>

namespace gpid {

    /** Problem loading utility class using a via constraint design pattern. */
    template<typename DeclarationsT>
    class ProblemConstraintsLoader {
    public:
        /** Enum form problem generation mode */
        enum class IOMode { READ, WRITE };
        /** Underlying interface context manager type */
        using ContextManagerT = typename DeclarationsT::ContextManagerT;
        /** Handled constraint type */
        using ConstraintT = typename DeclarationsT::ConstraintT;
    private:
        IOMode mode = IOMode::WRITE;

        ContextManagerT& ctx;
        DeclarationsT decls;

        std::vector<ConstraintT> cons_data;
        uint32_t reading_pos = -1;

        inline void initCurrentMode();
    public:
        /** Contructor */
        ProblemConstraintsLoader(ContextManagerT& ctx);
        ~ProblemConstraintsLoader();

        /** Set the functionning mode of the constraint loader. */
        inline void setMode(IOMode nmode) { mode = nmode; initCurrentMode(); }
        /** \return The underlying context manager. */
        inline ContextManagerT& getContextManager() { return ctx; }
        /** \return The underlying declarations. */
        inline DeclarationsT& getDeclarations() { return decls; }
        /** If in write mode, adds a loaded constraint. */
        inline void addConstraint(ConstraintT cons);
        /** If in read mode, check if more constraints have been loaded. */
        inline bool hasMoreConstraints();
        /** If in read mode, return the next loaded constraint (once). */
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
