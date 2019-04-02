/**
 * \file stdutils/pairstorage.hpp
 * \brief Structure for storing pairs and mapping then from both keys
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_STANDARD_UTILS__PAIR_STORAGE_HPP
#define LIB_STANDARD_UTILS__PAIR_STORAGE_HPP

#include <map>
#include <stdutils/collections.hpp>

namespace stdutils {

    template<class K0, class K1,
             class CompareFwd=std::less<K0>, class CompareBck=std::less<K1>,
             class AllocFwd=std::allocator<std::pair<const K0,K1>>,
             class AllocBck=std::allocator<std::pair<const K1,K0>>>
    class pair_storage {
    public:
        using forward_map_type = std::map<K0, K1, CompareFwd, AllocFwd>;
        using backward_map_type = std::map<K1, K0, CompareBck, AllocBck>;

        using forward_key_type     = typename forward_map_type::key_type;
        using backward_key_type    = typename backward_map_type::key_type;
        using forward_mapped_type  = typename forward_map_type::mapped_type;
        using backward_mapped_type = typename backward_map_type::mapped_type;

        using forward_value_type  = typename forward_map_type::value_type;
        using backward_value_type = typename backward_map_type::value_type;

        using forward_key_compare  = typename forward_map_type::key_compare;
        using backward_key_compare = typename backward_map_type::key_compare;

        using forward_allocator_type  = typename forward_map_type::allocator_type;
        using backward_allocator_type = typename backward_map_type::allocator_type;

        using forward_reference  = typename forward_map_type::reference;
        using forward_const_reference  = typename forward_map_type::const_reference;
        using backward_reference = typename backward_map_type::reference;
        using backward_const_reference = typename backward_map_type::const_reference;

        using iterator               = typename forward_map_type::iterator;
        using const_iterator         = typename forward_map_type::const_iterator;
        using reverse_iterator       = typename backward_map_type::iterator;
        using reverse_const_iterator = typename backward_map_type::const_iterator;

        using size_type = size_t;
    private:
        forward_map_type forward_map;
        backward_map_type backward_map;
    public:
        explicit pair_storage() {}
        pair_storage(const pair_storage& o)
            : forward_map(o.forward_map), backward_map(o.backward_map) {}

        pair_storage& operator=(const pair_storage& o) {
            forward_map = o.forward_map;
            backward_map = o.backward_map;
        }

        inline iterator               begin()         noexcept { return forward_map.begin();   }
        inline const_iterator         cbegin()  const noexcept { return forward_map.cbegin();  }
        inline iterator               end()           noexcept { return forward_map.end();     }
        inline const_iterator         cend()    const noexcept { return forward_map.cend();    }
        inline reverse_iterator       rbegin()        noexcept { return backward_map.begin();  }
        inline reverse_const_iterator crbegin() const noexcept { return backward_map.cbegin(); }
        inline reverse_iterator       rend()          noexcept { return backward_map.end();    }
        inline reverse_const_iterator crend()   const noexcept { return backward_map.cend();   }

        inline bool empty() const noexcept { return forward_map.empty(); }
        inline size_type size() const noexcept { return forward_map.size(); }
        inline size_type max_size() const noexcept {
            return forward_map.max_size() > backward_map.max_size() ?
                backward_map.max_size() : forward_map.max_size();
        }

        inline forward_mapped_type& at(const forward_key_type& k)
        { return forward_map.at(k); }
        inline const forward_mapped_type& at(const forward_key_type& k) const
        { return forward_map.at(k); }
        inline backward_mapped_type& rat(const backward_key_type& k)
        { return backward_map.at(k); }
        inline const backward_mapped_type& rat(const backward_key_type& k) const
        { return backward_map.at(k); }

        inline bool insert(const forward_key_type& k, const forward_mapped_type& v) {
            bool fwdb = forward_map.insert(forward_value_type(k, v)).second;
            bool bckb = backward_map.insert(backward_value_type(v, k)).second;
            return fwdb && bckb;
        }
        inline bool rinsert(const backward_key_type& k, const backward_mapped_type& v) {
            return insert(v, k);
        }

        inline size_type erase(const forward_key_type& k) { return forward_map.erase(k); }
        inline size_type rerase(const backward_key_type& k) { return backward_map.erase(k); }

        inline void clear() noexcept { forward_map.clear(); backward_map.clear(); }

        inline bool contains(const forward_key_type& k) const { return inmap(forward_map, k); }
        inline bool rcontains(const backward_key_type& k) const { return inmap(backward_map, k); }

    };

}

#endif
