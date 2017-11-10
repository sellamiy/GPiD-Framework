#define _GPID_SYSTEM_CPP_

#include <csignal>
#include <snlog/snlog.hpp>
#include <gpid/core/system.hpp>

static gpid::SystemInterruptsFlags* sys_flag_loc;

static void systemInterruptHandler(int signum) {
    snlog::l_fatal("Interrupted");
    snlog::l_info(signum);

    sys_flag_loc->interruption_flag = true;
}

extern void gpid::registerInterruptsHandlers(SystemInterruptsFlags* flags_addr) {
    sys_flag_loc = flags_addr;
    signal(SIGINT, systemInterruptHandler);
}

extern void gpid::restoreInterruptsHandlers() {
    sys_flag_loc = NULL;
    signal(SIGINT, SIG_DFL);
}
