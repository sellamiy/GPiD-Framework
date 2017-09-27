#ifndef GPID_MEMORY_HPP
#define GPID_MEMORY_HPP

#include <stdint.h>

namespace gpid {
    namespace memory {

        template <typename InternalT>
        class lv_tab {
            enum ltc_status { INACTIVE, SKIPPED, ACTIVE };
            struct ltc_elem { InternalT content; ltc_status status; uint32_t level; };

            uint32_t level;
        public:
            void extend(uint32_t lvl);
            void shrink(uint32_t lvl);

            bool has_next(uint32_t lvl);

            void set_current(uint32_t lvl);
            void unset_current(uint32_t lvl);
            void skip_current(uint32_t lvl);
            InternalT get_current(uint32_t lvl);
        };

        template <typename InternalT>
        inline void lv_tab<InternalT>::extend(uint32_t lvl) {
            // TODO
        }

    };
};

#endif
