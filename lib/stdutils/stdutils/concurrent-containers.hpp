/**
 * \file stdutils/concurrent-containers.hpp
 * \brief Concurrent containers implementation
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef LIB_STANDARD_UTILS__CONCURRENT_CONTAINERS_HPP
#define LIB_STANDARD_UTILS__CONCURRENT_CONTAINERS_HPP

#include <queue>
#include <vector>
#include <thread>
#include <mutex>
#include <condition_variable>

namespace stdutils {

    template <typename T>
    class ConcurrentQueue {
    private:
        std::queue<T> _data;
        std::mutex mtx;
        std::condition_variable cond;
    public:
        inline T pop();
        inline void push(const T& e);
        ConcurrentQueue() = default;
        ConcurrentQueue(const ConcurrentQueue&) = delete;
        ConcurrentQueue& operator=(const ConcurrentQueue&) = delete;
    };

    template <typename T>
    class ConcurrentVector {
    private:
        std::vector<T> _data;
        std::mutex mtx;
        std::condition_variable cond;
    public:
        inline T access(size_t idx);
        inline void store(const T& e);
        inline const std::vector<T>& extract() const { return _data; }
        inline size_t size() const { return _data.size(); }
        ConcurrentVector() = default;
        ConcurrentVector(const ConcurrentVector&) = delete;
        ConcurrentVector& operator=(const ConcurrentVector&) = delete;
    };

    template <typename T> inline T ConcurrentQueue<T>::pop() {
        std::unique_lock<std::mutex> mlock(mtx);
        while (_data.empty())
            cond.wait(mlock);
        auto tcp = _data.front();
        _data.pop();
        return tcp;
    }

    template <typename T> inline void ConcurrentQueue<T>::push(const T& e) {
        std::unique_lock<std::mutex> mlock(mtx);
        _data.push(e);
        mlock.unlock();
        cond.notify_one();
    }

    template <typename T> inline T ConcurrentVector<T>::access(size_t idx) {
        std::unique_lock<std::mutex> mlock(mtx);
        while (idx >= _data.size())
            cond.wait(mlock);
        auto tcp = _data.at(idx);
        return tcp;
    }

    template <typename T> inline void ConcurrentVector<T>::store(const T& e) {
        std::unique_lock<std::mutex> mlock(mtx);
        _data.push_back(e);
        mlock.unlock();
        cond.notify_one();
    }

}

#endif
