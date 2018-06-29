/**
 * \file gpid/utils/hprinters.hpp
 * \brief GPiD-Framework Literals handlers.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__UTILS__HYPOTHESES_PRINTERS_HPP
#define GPID_FRAMEWORK__UTILS__HYPOTHESES_PRINTERS_HPP

namespace gpid {

    template<typename InterfaceT, typename HypothesisT> class LiteralHypothesisPrinter;
    template<typename InterfaceT, typename HypothesisT> std::ostream& operator<<
    (std::ostream& os, const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& hlp);

    template<typename InterfaceT, typename HypothesisT>
    class LiteralHypothesisPrinter {
        HypothesisT& hypothesis;
        ObjectMapper<typename InterfaceT::LiteralT>& mapper;
        bool negate;
    public:
        LiteralHypothesisPrinter
        (HypothesisT& lh, ObjectMapper<typename InterfaceT::LiteralT>& mp, bool neg=true)
            : hypothesis(lh), mapper(mp), negate(neg) {}
        LiteralHypothesisPrinter(const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& o)
            : hypothesis(o.hypothesis), mapper(o.mapper), negate(o.negate) {}

        inline HypothesisT& getHypothesis() const { return hypothesis; }
        inline ObjectMapper<typename InterfaceT::LiteralT>& getMapper() const { return mapper; }
        inline bool isNegated() const { return negate; }

        friend std::ostream& operator<< <InterfaceT, HypothesisT>
        (std::ostream& os, const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& hlp);
    };

    template<typename InterfaceT, typename HypothesisT>
    inline const LiteralHypothesisPrinter<InterfaceT, HypothesisT> implicate
    (HypothesisT& h, ObjectMapper<typename InterfaceT::LiteralT>& mp) {
        return LiteralHypothesisPrinter<InterfaceT, HypothesisT>(h, mp, true);
    }

    template<typename InterfaceT, typename HypothesisT>
    inline const LiteralHypothesisPrinter<InterfaceT, HypothesisT> hypothesis
    (HypothesisT& h, ObjectMapper<typename InterfaceT::LiteralT>& mp) {
        return LiteralHypothesisPrinter<InterfaceT, HypothesisT>(h, mp, false);
    }

    template<typename InterfaceT, typename HypothesisT> std::ostream& operator<<
    (std::ostream& os, const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& hlp) {
        return InterfaceT::write(os, hlp.getHypothesis(), hlp.getMapper(), hlp.isNegated());
    }

    template<typename InterfaceT, typename HypothesisT>
    inline void printlh(const LiteralHypothesisPrinter<InterfaceT, HypothesisT>& p) {
        std::cout << "> " << p << std::endl;
    }

}

#endif
