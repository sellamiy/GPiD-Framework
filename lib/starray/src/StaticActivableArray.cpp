#define _STATIC_ACTIVABLE_ARRAY_CPP_

#include <stdlib.h>
#include <assert.h>
#include <starray/StaticActivableArray.hpp>

using namespace starray;

StaticActivableArray::StaticActivableArray(uint32_t size)
{
    assert(size > 0);
    total_size = size;
    activated_size = size;
    tab = (aa_elt_t *)calloc(size, sizeof(aa_elt_t));
    assert(tab);
    list_first.prev = size + 2;
    list_first.index = size;
    list_curr = &list_first;
    list_last.next = size + 2;
    list_last.index = size + 1;
    aa_elt_t *prev = &list_first;
    for (uint32_t i = 0; i < size; i++) {
        tab[i].value = 1;
        tab[i].index = i;
        tab[i].prev = prev->index;
        prev->next = i;
        prev = &(tab[i]);
    }
    tab[size - 1].next = size + 1;
    list_last.prev = size - 1;
}

StaticActivableArray::~StaticActivableArray()
{
    free(tab);
}

void StaticActivableArray::activate(uint32_t i)
{
    assert(i < total_size);
    if (!tab[i].value) {
        activated_size++;
        tab[i].value = 1;
        if (list_last.prev < total_size) {
            tab[list_last.prev].next = i;
        } else {
          list_first.next = i;
        }
        tab[i].prev = list_last.prev;
        tab[i].next = list_last.index;
        list_last.prev = i;
    }
}

void StaticActivableArray::deactivate(uint32_t i)
{
    assert(i < total_size);
    if (tab[i].value) {
        activated_size--;
        tab[i].value = 0;
        if (tab[i].next < total_size) {
            tab[tab[i].next].prev = tab[i].prev;
        } else {
            list_last.prev = tab[i].prev;
        }
        if (tab[i].prev < total_size) {
            tab[tab[i].prev].next = tab[i].next;
        } else {
            list_first.next = tab[i].next;
        }
        tab[i].prev = total_size + 2;
        tab[i].next = total_size + 2;
    }
}
