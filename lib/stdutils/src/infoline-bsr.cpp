#define LIB_STANDARD_UTILS__BACKSLASH_R_INFOLINE_CPP

#include <chrono>

#include <snlog/snlog.hpp>
#include <stdutils/infoline-bsr.hpp>

using namespace stdutils;

void BsRInfoliner::update() const {
    std::cout << "\r[";
    for (InfoDataPtr ptr : data)
        std::cout << *ptr << "  ";
    std::cout << "]" << std::flush;
}

void BsRInfoliner::setup() {
    interrupt = false;
    ilth = std::unique_ptr<std::thread>(new std::thread(&BsRInfoliner::loop, this));
}

void BsRInfoliner::discard() {
    interrupt = true;
    ilth->join();
    std::cout << std::endl;
}

void BsRInfoliner::loop() const {
    do {
        update();
        std::this_thread::sleep_for(std::chrono::milliseconds(ldelay));
    } while (!interrupt);
}

void BsRInfoliner::addInfoData(InfoDataPtr ptr) {
    data.push_back(ptr);
}
