#ifndef GPID_HYPOTHESES_HPP
#define GPID_HYPOTHESES_HPP

namespace gpid {

    template<class HypothesisT>
    class HypothesesSet {
    public:
        bool isEmpty(uint32_t level);
        HypothesisT& nextHypothesis(uint32_t level);
    };

};

#endif
