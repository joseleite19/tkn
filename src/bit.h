#ifndef BITSET
#define BITSET

typedef struct bitset{
    long long *v;
    int size;
    int limit;
}bitset;

int is_set(bitset*, int);
void set(bitset*, int);
void reset(bitset*, int);
bitset* create_set(int);
bitset* clean_set(bitset*);

#endif
