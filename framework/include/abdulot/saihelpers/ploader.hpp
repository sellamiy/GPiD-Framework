/**
 * \file abdulot/saihelpers/ploader.hpp
 * \brief Abdulot Problem loader generic template.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__SAI_HELPERS__PLOADER_HPP
#define ABDULOT__SAI_HELPERS__PLOADER_HPP

#include <vector>
#include <snlog/snlog.hpp>
#include <abdulot/core/errors.hpp>

namespace abdulot {
namespace saihelpers {

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
        snlog::t_warn(mode != IOMode::WRITE) << "Writing problem on reading mode" << snlog::l_end;
        cons_data.push_back(cons);
    }

    template<typename DeclarationsT>
    inline bool ProblemConstraintsLoader<DeclarationsT>::hasMoreConstraints() {
        snlog::t_warn(mode != IOMode::READ) << "Reading problem on writing mode" << snlog::l_end;
        return reading_pos < cons_data.size();
    }

    template<typename DeclarationsT>
    inline typename ProblemConstraintsLoader<DeclarationsT>::ConstraintT
    ProblemConstraintsLoader<DeclarationsT>::nextConstraint() {
        snlog::t_warn(mode != IOMode::READ) << "Reading problem on writing mode" << snlog::l_end;
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
            snlog::l_internal() << "Problem loader ended in an Unknown state!" << snlog::l_end;
            throw InternalError("Problem loader ended in an Unknown state!");
        }
    }

}
}

#endif
