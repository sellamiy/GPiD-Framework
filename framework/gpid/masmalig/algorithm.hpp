/**
 * \file gpid/masmalig/algorithm.hpp
 * \brief GPiD-Framework Magically Smart Literal Generator (via SMTlibv2).
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__MASMALIG__ALGORITHM_HPP
#define GPID_FRAMEWORK__MASMALIG__ALGORITHM_HPP

#include <mlbsmt2/mlbsmt2.hpp>
#include <gpid/core/algorithm.hpp>
#include <gpid/core/errors.hpp>
#include <gpid/reference/version.hpp>
#include <gpid/masmalig/options.hpp>

namespace gpid {

    /**
     * \brief Smart Literal Generator in/from SMTLibv2 Format.
     */
    template<typename LiteralHandlerT>
    class MasmaligAlgorithm : public GPiDAlgorithm {
    public:
    private:
        MasmaligOptions& options;
        mlbsmt2::MagicLiteralBuilder builder;

        LiteralHandlerT& lhandler;

        virtual void _execute() override;

    public:
        /** Generator initialization */
        MasmaligAlgorithm(LiteralHandlerT& lhandler, GPiDOptions& opts, MasmaligOptions& iopts);

        /** Print informations on the algorithm and its parameters. */
        static void printInfos();
    };

    /* *** Implementation *** */

    template<typename LiteralHandlerT>
    MasmaligAlgorithm<LiteralHandlerT>::MasmaligAlgorithm
    (LiteralHandlerT& lhandler, GPiDOptions& opts, MasmaligOptions& iopts)
        : GPiDAlgorithm(opts),
          options(iopts),
          lhandler(lhandler)
    {}

    template<typename LiteralHandlerT>
    void MasmaligAlgorithm<LiteralHandlerT>::printInfos() {
        snlog::l_message() << "GPiD framework somehow magically smart literal generator "
                           << project_version << snlog::l_end;
    }

    template<typename LiteralHandlerT>
    void MasmaligAlgorithm<LiteralHandlerT>::_execute() {

        for (std::string& target : options.targets) {
            try {
                builder.uses(mlbsmt2::productionTable.at(target));
            } catch (std::out_of_range& e) {
                throw UnknownUtilityError("Unknown production rule: " + target);
            }
        }

        if (!builder.valid()) {
            throw InternalError("Invalidly initialized Masmalig builder");
        }

        for (std::string filename : options.source_files) {
            builder.loadSMTlib2File(filename);
        }
        for (std::string filename : options.script_files) {
            builder.loadMlbScript(filename);
        }
        for (std::string filename : options.whyml_files) {
            builder.loadWhyMLFile(filename);
        }
        
        if (!builder.exploitable()) {
            throw DataError("Masmalig file loading resulted in corruption");
        }
        builder.exploitData();

        while (builder.buildable() && !iflags.systemInterrupted()) {
            lhandler.handle(builder.buildLiteral());
        }
        if (iflags.systemInterrupted()) {
            snlog::l_warn() << "Generation incomplete after interruption" << snlog::l_end;
        } else if (!builder.complete()) {
            snlog::l_warn() << "The following may be due to improper input" << snlog::l_end;
            throw InternalError("Masmalig generation failure");
        }
    }

}

#endif
