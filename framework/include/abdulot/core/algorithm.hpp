/**
 * \file abdulot/core/algorithm.hpp
 * \brief Abdulot-Framework Algorithm Instances.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__CORE__ALGORITHM_HPP
#define ABDULOT__CORE__ALGORITHM_HPP

#include <thread>
#include <abdulot/core/system.hpp>
#include <abdulot/core/options.hpp>

namespace abdulot {

    /** Base class for algorithmic utilities. */
    class Algorithm {
        std::unique_ptr<std::thread> execution_thread;
        void _terminate_execution();
        bool _execution_complete = false;
    protected:
        /** Options of the algorithm */
        AlgorithmOptions& options;
        /** Interruption flags for requesting an interruption */
        SystemInterruptionFlags iflags;

        /** Abstract method for actual algorithm execution. */
        virtual void _execute() = 0;

        /** Algorithm construction and parametrization. */
        Algorithm(AlgorithmOptions& o) : execution_thread(nullptr), options(o) {}
    public:
        /** Counter type for compting things. */
        using counter_t = uint64_t;

        /** Algorithm completion checker **/
        inline constexpr bool complete() const { return _execution_complete; }

        /** Main wrapper method for executing the algorithm. */
        void execute(bool in_thread=false);

        /** Thread interruption signaler */
        void interrupt();

        /** Thread joiner */
        void join();
    };

}

#endif
