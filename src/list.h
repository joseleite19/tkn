#ifndef LISTA
#define LISTA

#include <stdlib.h>
#include <stdio.h>
#include "tree.h"

typedef struct list{
  tnode *formula;
  struct list *next, *prev;
}list;

typedef struct header{
  list *begin, *end;
}header;

tnode *back(header *h);

tnode *front(header *h);

int empty(header *h);

void pop_back(header *h);

void pop_front(header *h);

void push_back(header *h, tnode *f);

void push_front(header *h, tnode *f);

void print(header *h);

header *create_list();

header *clean(header *h);
header *clean(header *h);

header *copy_header(header *h);

void erase(header *h, list *f);
void deserase(header *h, list *f);

extern tnode *copy_tree(tnode *);
extern tnode *free_tree(tnode *);
extern int print_tree(tnode *);
extern int same_tree(tnode *, tnode *);

#endif