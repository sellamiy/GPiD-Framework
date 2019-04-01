#define ABDULOT__SYSTEM_CPP

#include <csignal>
#include <thread>
#include <chrono>
#include <vector>
#include <snlog/snlog.hpp>
#include <abdulot/core/system.hpp>

static std::vector<abdulot::SystemInterruptionFlags*> sys_flag_locs;

static void systemInterruptHandler(int signum) {
    snlog::l_fatal() << "Interrupted" << snlog::l_end;
    snlog::l_info() << signum << snlog::l_end;

    for (abdulot::SystemInterruptionFlags* irf : sys_flag_locs)
        irf->interrupt(abdulot::SystemInterruptionFlags::Reason::__USER);
}

extern void abdulot::registerInterruptionHandlers(SystemInterruptionFlags* flags_addr) {
    bool signal_change_required = sys_flag_locs.empty();
    sys_flag_locs.push_back(flags_addr);
    if (signal_change_required) {
        signal(SIGINT, systemInterruptHandler);
    }
}

extern void abdulot::restoreInterruptionHandlers() {
    sys_flag_locs.pop_back();
    if (sys_flag_locs.empty()) {
        signal(SIGINT, SIG_DFL);
    }
}

class systemTimeoutWaiter {
    abdulot::SystemInterruptionFlags* external_flags_addr;
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
        snlog::l_fatal() << "Timeout" << snlog::l_end;
        external_flags_addr->interrupt(abdulot::SystemInterruptionFlags::Reason::__TIMEOUT);
    }

    std::thread* sys_timeout_waiter = NULL;
public:
    systemTimeoutWaiter(abdulot::SystemInterruptionFlags* flags_addr, uint64_t time_limit)
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

extern void abdulot::startTimeout(SystemInterruptionFlags* flags_addr, uint64_t timeout) {
    if (timeout > 0) {
        sys_timeout_waiter = new systemTimeoutWaiter(flags_addr, timeout);
        sys_timeout_waiter->start();
    }
}

extern void abdulot::stopTimeout() {
    if (sys_timeout_waiter != NULL) {
        sys_timeout_waiter->stop();
        delete sys_timeout_waiter;
    }
}
