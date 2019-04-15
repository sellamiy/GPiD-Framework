/**
 * \file abdulot/ilinva/abdgen-dual.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__ILINVA__DUAL_SOMEHOW_SMART_ABDUCIBLE_GENERATION_HPP
#define ABDULOT__ILINVA__DUAL_SOMEHOW_SMART_ABDUCIBLE_GENERATION_HPP

#include <abdulot/ilinva/data-dual.hpp>

namespace abdulot {
namespace ilinva {

    template<typename CodeHandlerT, typename InterfaceT>
    class SomehowSmartDualAbducibleGenerator {
        using CodeConstraintListT = std::vector<typename CodeHandlerT::ConstraintT>;

        ObjectMapper<typename InterfaceT::LiteralT> mapper;
        std::map<uint32_t, std::vector<uint32_t>> links;
    public:
        SomehowSmartDualAbducibleGenerator
        (const CodeConstraintListT& constraints, typename InterfaceT::ContextManagerT& ctx) {
            const std::string mra_id = std::to_string((uintptr_t)this);
            memoryRangeAllocation<typename InterfaceT::LiteralT>(mra_id, constraints.size());
            uint32_t mid = 0;
            for (const typename CodeHandlerT::ConstraintT& cons : constraints) {
                memoryObjectAllocation(mra_id, mid++, mapper,
                                       convert<CodeHandlerT, InterfaceT>(cons, ctx));
            }
        }

        ~SomehowSmartDualAbducibleGenerator() {
            memoryRangeRelease(std::to_string((uintptr_t)this));
        }

        inline size_t count() {
            return mapper.size();
        }

        inline ObjectMapper<typename InterfaceT::LiteralT>& getMapper() {
            return mapper;
        }
        inline std::map<uint32_t, std::vector<uint32_t>>& getLinks() {
            return links;
        }
    };

}
}

#endif
