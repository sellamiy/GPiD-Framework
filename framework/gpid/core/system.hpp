/**
 * \file gpid/core/system.hpp
 * \brief GPiD-Framework Platform system utilities.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__SYSTEM_HPP
#define GPID_FRAMEWORK__CORE__SYSTEM_HPP

#include <cstdint>

namespace gpid {

    /** \brief System interruption flag storage. */
    struct SystemInterruptionFlags {
        /** Possible reasons for an interruption */
        enum class SystemInterruptionReason {
            /** No particular reason */
            SYS_INT_R__,
            /** Engine internal: the engine internally decides to interrupt */
            SYS_INT_R__INTERNAL,
            /** User interruption */
            SYS_INT_R__USER,
            /** Timeout */
            SYS_INT_R__TIMEOUT
        };
        /** Interruption reason type */
        using Reason = SystemInterruptionReason;
        /** Reason of the interruption */
        SystemInterruptionReason reason = Reason::SYS_INT_R__;
        /** Interruption flag. Set to true iff the engine should be interrupted. */
        bool interruption_flag = false;

        /** Signal an interruption request. */
        inline void interrupt(SystemInterruptionReason r) {
            interruption_flag = true;
            reason = r;
        }
        /** \return true iff at least one interruption flag is set. */
        inline bool systemInterrupted() { return interruption_flag; }
        /** \return The last interruption request's reason. */
        inline SystemInterruptionReason getReason() { return reason; }
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
