#include "bit.h"
#include <stdlib.h>

int is_set(bitset* b, int id){
    return (b->v[id >> 6] & (1 << (id & 0x3f))) != 0;
}

void set(bitset *b, int id){
    b->v[id >> 6] |= (1 << (id & 0x3f));
}

void reset(bitset *b, int id){
    b->v[id >> 6] &= ~(1 << (id & 0x3f));
}

bitset* create_set(int sz){
    bitset* b = malloc(sizeof(bitset));
    b->size = sz;
    b->limit = (sz+63)>>6;
    b->v = calloc(b->limit, sizeof(long long));
    return b;
}

bitset* clean_set(bitset* b){
    if(b){
        free(b->v);
        free(b);
    }

    return NULL;
}


