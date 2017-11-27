/**
 * \file gpid/core/system.hpp
 * \brief GPiD-Framework Platform system utilities.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__SYSTEM_HPP
#define GPID_FRAMEWORK__CORE__SYSTEM_HPP

namespace gpid {

    /** \brief System interruption flag storage. */
    struct SystemInterruptsFlags {
        /** Engine internal flag. Set to true iff the engine internally decides it. */
        bool internal_flag = false;
        /** User interruption flag. Set to true iff user interrupted the engine. */
        bool interruption_flag = false;
        /** Timeout flag. Set to true iff computation time exceeded the limit. */
        bool timeout_flag = false;
        /** \return true iff at least one interruption flag is set. */
        inline bool systemInterrupted() {
            return internal_flag || interruption_flag || timeout_flag;
        }
    };

    /**
     * \brief Configure the system interruption handler for setting local flags on interruption.
     * \param flags_addr Location of the engine flags.
     */
    extern void registerInterruptsHandlers(SystemInterruptsFlags* flags_addr);
    /** \brief Restore system default interruption handlers. */
    extern void restoreInterruptsHandlers();

    /**
     * \brief Start a timeout.
     * \param flags_addr Location of the flags to set on timeout.
     * \param timeout Timeout in seconds.
     */
    extern void startTimeout(SystemInterruptsFlags* flags_addr, uint64_t timeout);
    /** \brief Stop the current timeout evolution. */
    extern void stopTimeout();

}

#endif
