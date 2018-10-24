/**
 * \file infoline/bsr-infoline.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef LIB_INFOLINE__BACKSLASH_R_INFOLINE_HPP
#define LIB_INFOLINE__BACKSLASH_R_INFOLINE_HPP

#include <map>
#include <string>
#include <vector>
#include <memory>
#include <thread>
#include <ostream>

#define BSR_INFOLINE_UPDATE_DELAY 1000

namespace infoline {

    struct InfoData {
        InfoData(const std::string& dname) : dname(dname) {}
        const std::string dname;
        virtual std::string str() const = 0;
    };

    inline std::ostream& operator<<(std::ostream& out, const InfoData& d) {
        return out << d.dname << ":" << d.str();
    }

    using InfoDataPtr = std::shared_ptr<InfoData>;

    template <typename O, typename Stringify>
    class PointerInfoData : public InfoData {
        std::shared_ptr<O> _ptr;
        Stringify stringifier;
    public:
        PointerInfoData(const std::string& dname, std::shared_ptr<O> ptr)
            : InfoData(dname), _ptr(ptr) {}
        PointerInfoData(const std::string& dname, const O& data)
            : InfoData(dname), _ptr(new O(data)) {}
        PointerInfoData(const PointerInfoData<O, Stringify>& o)
            : InfoData(o.dname), _ptr(o._ptr) {}
        virtual std::string str() const override {
            return stringifier(*_ptr);
        }
    };

    class BsRInfoliner {
        std::vector<InfoDataPtr> data;
        std::unique_ptr<std::thread> ilth;
        int ldelay = BSR_INFOLINE_UPDATE_DELAY;
        bool interrupt;
        void update() const;
        void loop() const;
    public:
        BsRInfoliner() = default;
        BsRInfoliner(const std::vector<InfoDataPtr>& data) : data(data) {}
        void addInfoData(InfoDataPtr ptr);

        void setup();
        void discard();
    };

}

#endif
