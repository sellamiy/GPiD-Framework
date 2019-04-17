/**
 * \file abdulot/gpid/options.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__GPID__OPTIONS_HPP
#define ABDULOT__GPID__OPTIONS_HPP

#include <limits>
#include <abdulot/core/saitypes.hpp>

namespace abdulot {
namespace gpid {

    /** Method selector for obtaining abducible literals. */
    enum class AbducibleInputType { FILE, GENERATOR };
    /** String converter for AbducibleInputType. */
    inline const std::string to_string(const AbducibleInputType& it)
    { return it == AbducibleInputType::FILE ? "Abd?Type:file" : "Abd?Type:generator"; }

    /** Options for the implicate generator algorithm. */
    struct GPiDOptions {

        /** Print implicates on terminal when generated */
        bool print_implicates = false;
        /** Store generated implicates and skipp storage-subsumed hypotheses */
        bool store_implicates = true;
        /** Print stored implicates after computation */
        bool print_storage = false;
        /** Export stored implicates as graph after computation */
        bool export_storage = false;
        /** Location to export storage to */
        std::string export_storage_location;

        /** Use models returned by solvers to filter hypotheses */
        bool use_models = true;

        /** Do not skip inconsistent hypotheses sets */
        bool allow_inconsistencies = false;

        bool preprune_literals = false;

        /** Skip literals detected as consequences of previous assignments */
        bool detect_consequences = false;

        bool additional_checker = false;
        SolverTestStatus additional_check_mode = SolverTestStatus::UNSAT;

        bool external_checker = false;

        /** Treat unknown solver */
        SolverTestStatus unknown_handle = SolverTestStatus::UNKNOWN;

        /** Maximal number of abducible hypotheses in an implicate */
        uint32_t max_level = std::numeric_limits<uint32_t>::max();

        /** Maximal number of implicates to generate */
        uint64_t implicate_limit = std::numeric_limits<uint64_t>::max();

        /** Method for recovering abducibles hypotheses */
        AbducibleInputType input_type = AbducibleInputType::GENERATOR;
        /** If input_type == FILE, filename to load hypotheses from */
        std::string input_file;
        /** If input_type == GENERATOR, id of an hypotheses generator */
        std::string input_generator = "<none>";

        uint64_t smt_time_limit = 0;
        double small_smt_time_limit = 0;

        std::map<std::string, std::string> translation_map;

    };

    static inline const SolverInterfaceOptions extractInterfaceOptions(const GPiDOptions& iopts) {
        return iopts.small_smt_time_limit > 0 ?
            SolverInterfaceOptions(iopts.small_smt_time_limit, iopts.translation_map)
            : SolverInterfaceOptions(iopts.smt_time_limit, iopts.translation_map);
    }

}
}

#endif
