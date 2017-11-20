#define _GPID_SYSTEM_CPP_

#include <csignal>
#include <thread>
#include <chrono>
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

class systemTimeoutWaiter {
    gpid::SystemInterruptsFlags* external_flags_addr;
    std::chrono::seconds s_time_limit;
    std::chrono::high_resolution_clock::time_point origin_date, current_date;
    bool autostop_flag;

    void run() {
        auto max_duration = std::chrono::duration_cast<std::chrono::seconds>(s_time_limit);
        origin_date = std::chrono::high_resolution_clock::now();
        current_date = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::seconds>(current_date - origin_date);
        while(duration < max_duration) {
            if (autostop_flag) return;
            current_date = std::chrono::high_resolution_clock::now();
            duration = std::chrono::duration_cast<std::chrono::seconds>(current_date - origin_date);
        }
        snlog::l_fatal("Timeout");
        external_flags_addr->timeout_flag = true;
    }

    std::thread* sys_timeout_waiter = NULL;
public:
    systemTimeoutWaiter(gpid::SystemInterruptsFlags* flags_addr, uint64_t time_limit)
        : external_flags_addr(flags_addr),
          s_time_limit(time_limit),
          autostop_flag(false)
    { }
    void start() {
        sys_timeout_waiter = new std::thread(&systemTimeoutWaiter::run, this);
    }
    void stop() {
        autostop_flag = true;
        sys_timeout_waiter->join();
        delete sys_timeout_waiter;
    }
};

static systemTimeoutWaiter* sys_timeout_waiter = NULL;

extern void gpid::startTimeout(SystemInterruptsFlags* flags_addr, uint64_t timeout) {
    if (timeout > 0) {
        sys_timeout_waiter = new systemTimeoutWaiter(flags_addr, timeout);
        sys_timeout_waiter->start();
    }
}

extern void gpid::stopTimeout() {
    if (sys_timeout_waiter != NULL) {
        sys_timeout_waiter->stop();
        delete sys_timeout_waiter;
    }
}
