#ifndef GPID_FRAMEWORK__CORE__SYSTEM_HPP
#define GPID_FRAMEWORK__CORE__SYSTEM_HPP

namespace gpid {

    struct SystemInterruptsFlags {
        bool interruption_flag = false;
        bool timeout_flag = false;
        inline bool systemInterrupted() {
            return interruption_flag || timeout_flag;
        }
    };

    extern void registerInterruptsHandlers(SystemInterruptsFlags* flags_addr);
    extern void restoreInterruptsHandlers();

    extern void startTimeout(SystemInterruptsFlags* flags_addr, uint64_t timeout);
    extern void stopTimeout();

}

#endif
