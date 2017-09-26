#ifndef GPID_MEMORY_HPP
#define GPID_MEMORY_HPP

#include <stdint.h>

namespace gpid {
    namespace memory {

        template <typename InternalT>
        class lv_tab {
        public:
            void extend(uint32_t level);
            void shrink(uint32_t level);

            bool has_next(uint32_t level);

            void set_current(uint32_t level);
            void unset_current(uint32_t level);
            void skip_current(uint32_t level);
            InternalT get_current(uint32_t level);
        };

    };
};

#endif
