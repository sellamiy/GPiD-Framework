/**
 * \file abdulot/core/system.hpp
 * \brief Abdulot Framework Platform system utilities.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__CORE__SYSTEM_HPP
#define ABDULOT__CORE__SYSTEM_HPP

#include <cstdint>

namespace abdulot {

    /** \brief System interruption flag storage. */
    struct SystemInterruptionFlags {
        /** Possible reasons for an interruption */
        enum class SystemInterruptionReason {
            /** No particular reason */
            __,
            /** Engine internal: the engine internally decides to interrupt */
            __INTERNAL,
            /** User interruption */
            __USER,
            /** Timeout */
            __TIMEOUT,
            /** Interrupted by parent caller */
            __PARENT
        };
        /** Interruption reason type */
        using Reason = SystemInterruptionReason;
        /** Reason of the interruption */
        SystemInterruptionReason reason = Reason::__;
        /** Interruption flag. Set to true iff the engine should be interrupted. */
        bool interruption_flag = false;

        /** Signal an interruption request. */
        inline void interrupt(SystemInterruptionReason r) {
            interruption_flag = true;
            reason = r;
        }
        /** \return true iff at least one interruption flag is set. */
        inline constexpr bool systemInterrupted() const { return interruption_flag; }
        /** \return The last interruption request's reason. */
        inline SystemInterruptionReason getReason() const { return reason; }
    };

    /**
     * \brief Configure the system interruption handler for setting local flags on interruption.
     * \param flags_addr Location of the engine flags.
     */
    extern void registerInterruptionHandlers(SystemInterruptionFlags* flags_addr);
    /** \brief Restore system default interruption handlers. */
    extern void restoreInterruptionHandlers();

    /**
     * \brief Start a timeout.
     * \param flags_addr Location of the flags to set on timeout.
     * \param timeout Timeout in seconds.
     */
    extern void startTimeout(SystemInterruptionFlags* flags_addr, uint64_t timeout);
    /** \brief Stop the current timeout evolution. */
    extern void stopTimeout();

}

#endif
