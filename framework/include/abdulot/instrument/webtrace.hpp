/**
 * \file abdulot/instrument/webtrace.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT_FRAMEWORK__INSTRUMENT__WEBTRACE_HPP
#define ABDULOT_FRAMEWORK__INSTRUMENT__WEBTRACE_HPP

#include <stdutils/traces-bootstrap.hpp>

namespace abdulot {
namespace instrument {

    /**
     * \brief Class for logging and exporting a web log of the computation.
     * \ingroup abdulotinstrumentlib
     */
    class WebtraceInstrument {

        stdutils::Trace tracelog;
        std::ostream& target;
        
    public:
        WebtraceInstrument(std::ostream& target)
            : tracelog(), target(target) {}

        void subcall(const std::string selected);
        void end_subcall();
        void command(const std::string c);
        void assign(const std::string k, const std::string v);

        void reset();
        void terminate();
    };

}
}

#endif
