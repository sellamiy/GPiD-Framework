#define _SEQUENTIAL_ACTIVABLE_ARRAY_CPP_

#include <cstdlib>
#include <cassert>
#include <snlog/snlog.hpp>
#include <starray/SequentialActivableArray.hpp>

using namespace starray;

SequentialActivableArray::SequentialActivableArray(uint32_t size)
{
    assert(size > 0);
    total_size = size;
    active_size = size;
    tab = (aa_elt_t *)calloc(size, sizeof(aa_elt_t));
    assert(tab);
    for (uint32_t i = 0; i < size; i++) {
        tab[i].status = aa_elt_st::ACTIVE;
        tab[i].index = i;
    }
}

SequentialActivableArray::~SequentialActivableArray()
{
    free(tab);
}

void SequentialActivableArray::activate(uint32_t i)
{
    if (tab[i].status != aa_elt_st::ACTIVE) active_size++;
    tab[i].status = aa_elt_st::ACTIVE;
}

void SequentialActivableArray::pause(uint32_t i)
{
    if (tab[i].status == aa_elt_st::ACTIVE) active_size--;
    tab[i].status = aa_elt_st::PAUSED;
}

void SequentialActivableArray::deactivate(uint32_t i)
{
    if (tab[i].status == aa_elt_st::ACTIVE) active_size--;
    tab[i].status = aa_elt_st::INACTIVE;
}

uint32_t SequentialActivableArray::get_last()
{
    uint32_t pos = total_size;
    do {
        pos--;
    } while(tab[pos].status == aa_elt_st::INACTIVE);
    return pos;
}

uint32_t SequentialActivableArray::get_first()
{
    uint32_t pos = 0;
    while (tab[pos].status == aa_elt_st::INACTIVE) {
        pos++;
    }
    return pos;
}
