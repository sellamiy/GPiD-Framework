#ifndef _GPID_SYSTEM_HPP_
#define _GPID_SYSTEM_HPP_

namespace gpid {

    struct SystemInterruptsFlags {
        bool interruption_flag = false;
        inline bool systemInterrupted() {
            return interruption_flag;
        }
    };

    extern void registerInterruptsHandlers(SystemInterruptsFlags* flags_addr);
    extern void restoreInterruptsHandlers();

}

#endif
