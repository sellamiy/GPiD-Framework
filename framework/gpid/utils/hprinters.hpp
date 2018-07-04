/**
 * \file gpid/utils/hprinters.hpp
 * \brief GPiD-Framework Literals printing handlers.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__UTILS__HYPOTHESES_PRINTERS_HPP
#define GPID_FRAMEWORK__UTILS__HYPOTHESES_PRINTERS_HPP

namespace gpid {

    template<typename InterfaceT, typename HypothesisT> class LiteralHypothesisPrinter;
    /** Literal conjunction printer flow operator. */
    template<typename InterfaceT, typename HypothesisT> std::ostream& operator<<
    (std::ostream& os, const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& hlp);

    /** Generic literal conjunction printer class. */
    template<typename InterfaceT, typename HypothesisT>
    class LiteralHypothesisPrinter {
        HypothesisT& hypothesis;
        ObjectMapper<typename InterfaceT::LiteralT>& mapper;
        typename InterfaceT::ContextManagerT& ctx;
        bool negate;
    public:
        /** Initialization of a literal conjunction printer. */
        LiteralHypothesisPrinter
        (HypothesisT& lh, ObjectMapper<typename InterfaceT::LiteralT>& mp,
         typename InterfaceT::ContextManagerT& ctx, bool neg=true)
            : hypothesis(lh), mapper(mp), ctx(ctx), negate(neg) {}
        /** Copy constructor */
        LiteralHypothesisPrinter(const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& o)
            : hypothesis(o.hypothesis), mapper(o.mapper), ctx(o.ctx), negate(o.negate) {}

        /** \return The underlying literal conjunction to print. */
        inline HypothesisT& getHypothesis() const { return hypothesis; }
        /** \return The underlying mapper from literal reference to literals. */
        inline ObjectMapper<typename InterfaceT::LiteralT>& getMapper() const { return mapper; }
        /** \return The underlying interface context manager. */
        inline typename InterfaceT::ContextManagerT& getContextManager() const { return ctx; }
        /** \return True iff the conjunction should be printed as a clause. */
        inline bool isNegated() const { return negate; }

        /** Literal conjunction printer flow operator. */
        friend std::ostream& operator<< <InterfaceT, HypothesisT>
        (std::ostream& os, const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& hlp);
    };

    /** Build an implicate (clause) printer from a literal conjunction. */
    template<typename InterfaceT, typename HypothesisT>
    inline const LiteralHypothesisPrinter<InterfaceT, HypothesisT> implicate
    (HypothesisT& h, ObjectMapper<typename InterfaceT::LiteralT>& mp,
     typename InterfaceT::ContextManagerT& ctx) {
        return LiteralHypothesisPrinter<InterfaceT, HypothesisT>(h, mp, ctx, true);
    }

    /** Build a conjunction printer from a literal conjunction. */
    template<typename InterfaceT, typename HypothesisT>
    inline const LiteralHypothesisPrinter<InterfaceT, HypothesisT> hypothesis
    (HypothesisT& h, ObjectMapper<typename InterfaceT::LiteralT>& mp,
     typename InterfaceT::ContextManagerT& ctx) {
        return LiteralHypothesisPrinter<InterfaceT, HypothesisT>(h, mp, ctx, false);
    }

    template<typename InterfaceT, typename HypothesisT> std::ostream& operator<<
    (std::ostream& os, const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& hlp) {
        return InterfaceT::write(os, hlp.getContextManager(), hlp.getHypothesis(),
                                 hlp.getMapper(), hlp.isNegated());
    }

    /** Formatter for printing literal hypotheses. */
    template<typename InterfaceT, typename HypothesisT>
    inline void printlh(const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& p) {
        std::cout << "> " << p << std::endl;
    }

}

#endif
