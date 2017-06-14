#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include "parser.tab.h"
#include "prover.h"
#include "symbol_table.h"
#include "uthash.h"
#include "list.h"
#include "tree.h"
#include "bit.h"
// #define USESATCACHE

int is_alpha(tnode *);
int is_modal(tnode *);

int phase = 0;
int OUT = 0;

int *cneg;

/* global variables for the prover options */

extern FILE *yyin;

/* variables in tokeniser.l */

extern int yylex_destroy();

extern int yy_scan_string(const char *);

extern tnode *input_preprocessing (tnode *);

tnode *root; // pointer for the root of the syntatic tree
// int newtemp; // number of new propositional symbols

extern void clear_hashes (void);
extern void clear_all (void);

extern int print_tree(tnode *s);
extern int same_tree(tnode*, tnode*);
extern unsigned int hash_tree (tnode *t);
extern tnode *free_tree (tnode *s);
extern void clean_ren_hash(void);
extern void symbol_table_init(void);
extern unsigned int hash_list(formulalist *);
extern header *clean_free_tree(header *);

int numearlyple;
int numearlymlple;

int linearise, prenex, early_ple, early_mlple, nnfsimp, bnfsimp;

void insere(header *alpha, header *beta, header *gama, header *delta, tnode *f){
  if(f->type == DIAMOND) push_back(delta, f->left);
  else if(f->type == BOX) push_back(gama, f->left);
  else if(f->type == CONJUNCTION) push_back(alpha, f);
  else push_back(beta, f);
}

void tira(header *alpha, header *beta, header *gama, header *delta, tnode *f){
  if(f->type == DIAMOND) pop_back(delta);
  else if(f->type == BOX) pop_back(gama);
  else if(f->type == CONJUNCTION) pop_back(alpha);
  else pop_back(beta);
}

typedef struct hash{
  unsigned int key;
  formulalist *list;
  UT_hash_handle hh;
}hash;

tnode *find(hash **set, tnode *f){
    hash *s;
    HASH_FIND(hh, *set, &f->value_number, sizeof(unsigned int), s);
    if(!s) return NULL;
    formulalist *tmp;
    for(tmp = s->list; tmp; tmp = tmp->next)
        if(same_tree(tmp->formula, f))
            return tmp->formula;
    return NULL;
}

void add(hash **set, tnode *f){
    if(!f) return;
    hash *s = NULL;
    HASH_FIND(hh, *set, &f->value_number, sizeof(unsigned int), s);

    if(s == NULL){
        s = malloc(sizeof(hash));
        s->key = f->value_number;
        s->list = NULL;
        HASH_ADD(hh, *set, key, sizeof(unsigned int), s);
    }

    formulalist *fl = malloc(sizeof(formulalist));
    fl->formula = f;
    fl->next = s->list;
    s->list = fl;
}

/*void del(hash **set, tnode *f){
  hash *s = find(set, f->value_number);
  HASH_DELETE(hh, *set, s);
  free(s);
}*/

int exists(bitset *set, tnode *f){
    if(!f) return 0;
    if(f->type == CONSTANT && f->id == CTRUE) return 1;
    if(f->type == CONSTANT && f->id == CFALSE) return 0;

    return is_set(set, f->value_number);
}

int existsneg(bitset *set, tnode *f){
    if(!f) return 0;
    if(f->type == CONSTANT && f->id == CFALSE) return 1;
    if(f->type == CONSTANT && f->id == CTRUE) return 0;
    if(cneg[f->value_number] == -1) return 0;
    //printf("asd %d %d\n", f->value_number, cneg[f->value_number]);
    return is_set(set, cneg[f->value_number]);
}

void clean_hash(hash **set){
    hash *tmp, *tmp2;
    formulalist *tt, *tt2;

    HASH_ITER(hh, *set, tmp, tmp2){
        for(tt = tmp->list; tt; tt = tt2){
            tt2 = tt->next;
            free(tt);
        }
        HASH_DELETE(hh, *set, tmp);
        free(tmp);
    }
}

struct cache{ //circular list
    bitset *s;
    struct cache *next;
};

struct cache *globalcache;
struct cache *globalsatcache;
int sz, szsat, limitsizecache = 2*4096;

long long cost;
long long costsat;

void encache(bitset **s){
    clock_t start = clock();
    if(sz < limitsizecache) sz++;
    else{
        struct cache *tmp = globalcache->next; //onde tem que ser apagado
        globalcache->next = globalcache->next->next;
        tmp->s = clean_set(tmp->s);
        free(tmp);
    }

    struct cache *tmp = (struct cache *)malloc(sizeof(struct cache));
    tmp->s = *s;
    tmp->next = globalcache->next;
    globalcache->next = tmp;
    globalcache = tmp;

    *s = NULL;
    cost += clock() - start;
}

int issubset(bitset *ss){
    clock_t start = clock();
    int i;

    struct cache *ptr = globalcache;
    int sub, cnt = 0;

    do{
        sub = 1;
        cnt = 0;
        for(i = 0; i < ptr->s->limit; i++){
            if((ss->v[i] & ptr->s->v[i]) != ptr->s->v[i]){
                sub = 0;
                break;
            }
        }
        if(!cnt) sub = 0;
        if(sub){
            cost += clock() - start;
            return 1;
        }
        ptr = ptr->next;
    }while(ptr != globalcache);

    cost += clock() - start;
    return 0;
}

void encachesat(hash **s){
  clock_t start = clock();
  /*if(szsat < limitsizecache) szsat++;
  else{
    struct cache *tmp = globalsatcache->next; //onde tem que ser apagado
    globalsatcache->next = globalsatcache->next->next;
    clean_hash(&(tmp->s));
    free(tmp);
  }
  // hash *tmp, *tmp2;
  struct cache *newcache = (struct cache *)malloc(sizeof(struct cache));

  newcache->s = *s;
  // HASH_ITER(hh, *s, tmp, tmp2){
  //   add(&(newcache->s), tmp->formula);
  // }
  newcache->next = globalsatcache->next;
  globalsatcache->next = newcache;
  globalsatcache = newcache;

  *s = NULL;*/
  cost += clock() - start;
}

int issubsetsat(hash *set){
  clock_t start = clock();
  /*hash *tmp, *tmp2;

  struct cache *ptr = globalsatcache;
  int sub, cnt = 0;

  do{
    sub = 1;
    cnt = 0;
    HASH_ITER(hh, set, tmp, tmp2){
      cnt++;
      if(!exists(&(ptr->s), tmp->formula)){
        sub = 0;
        break;
      }
    }
    if(!cnt) sub = 0;
    if(sub){
      costsat += clock() - start;
      return 1;
    }
    ptr = ptr->next;
  }while(ptr != globalsatcache);*/

  costsat += clock() - start;
  return 0;
}

extern void print_symbols_tables();

int op(tnode *t){
  if(!t) return 0;
  return (t->type == CONJUNCTION) || (t->type == DISJUNCTION) ||
         (t->type == BOX) || (t->type == DIAMOND);  
}

int is_alpha(tnode *f){
  if(!f) return 0;
  return f->type == CONJUNCTION;
}

formulalist *regra(tnode *f){
  if(f) if(f->type == CONJUNCTION || f->type == DISJUNCTION) return f->list;
  return NULL;
}

int is_false(tnode *t){
  return (t && t->type == CONSTANT && t->id == CFALSE);
}

int is_true(tnode *t){
  return (t && t->type == CONSTANT && t->id == CTRUE);
}

int is_modal(tnode *t){
  if(!t) return 0;
  return (t && t->type == BOX) || (t->type == DIAMOND);
}

int globalcounter = 0;

void passatudo(tnode *t){
  if(!t) return;
  passatudo(t->left);
  passatudo(t->right);
  formulalist *tmp;
  for(tmp = t->list; tmp; tmp = tmp->next)
    passatudo(tmp->formula);
}


int neww;

int dfs(header *alpha, header *beta, header *gama, header *delta, bitset *ss, int w){
    int fechou = 0;
    globalcounter++;
    formulalist *p = NULL;

    list *tmp = NULL;
    list *aux = NULL;

    header *cleandepois = create_list();

    header *copiaAlpha = create_list();
    for(aux = alpha->begin; aux && !fechou; aux = aux->next){

        for(p = regra(aux->formula); p; p = p->next){
            if(!exists(ss, p->formula)){

                if(existsneg(ss, p->formula)){
                    fechou = 1;
                    break;
                }
                else{
                    set(ss, p->formula->value_number);
                    push_back(cleandepois, p->formula);

                    if(op(p->formula)){
                        insere(copiaAlpha, beta, gama, delta, p->formula);
                    }
                }
            }
        }    
    }

    for(aux = copiaAlpha->begin; aux && !fechou; aux = aux->next){

        for(p = regra(aux->formula); p; p = p->next){
            if(!exists(ss, p->formula)){

                if(existsneg(ss, p->formula)){
                    fechou = 1;
                    break;
                }
                else{
                    set(ss, p->formula->value_number);
                    push_back(cleandepois, p->formula);

                    if(op(p->formula)){
                        insere(copiaAlpha, beta, gama, delta, p->formula);
                    }
                }
            }
        }
    }
    copiaAlpha = clean(copiaAlpha);


    if(!fechou){
        if(!empty(beta)){
            header *newAlpha = create_list();
            fechou = 1;

            aux = beta->begin;

            p = regra(aux->formula);

            erase(beta, aux);

            for(; p && fechou; p = p->next){
                if(!existsneg(ss, p->formula)){
                    if(!exists(ss, p->formula)){
                        set(ss, p->formula->value_number);
                        if(op(p->formula)){
                            insere(newAlpha, beta, gama, delta, p->formula);

                            fechou = dfs(newAlpha, beta, gama, delta, ss, w);

                            tira(newAlpha, beta, gama, delta, p->formula);
                        }
                        else{
                            fechou = dfs(newAlpha, beta, gama, delta, ss, w);
                        }
                        reset(ss, p->formula->value_number);
                    }
                    else{
                        fechou = dfs(newAlpha, beta, gama, delta, ss, w);
                    }
                }
            }
            deserase(beta, aux);

            newAlpha = clean(newAlpha);
        }
        else if(!empty(delta)){
            header *newAlpha = create_list();
            header *newBeta = create_list();
            header *newGama = create_list();
            header *newDelta = create_list();

            bitset *newss = create_set(ss->size);

            fechou = 0;
            int size = 0;
            for(tmp = gama->begin; tmp; tmp = tmp->next){
                if(existsneg(newss, tmp->formula)){ fechou = 1; break; }
                if(!exists(newss, tmp->formula)){
                    size++;
                    set(newss, tmp->formula->value_number);
                    if(issubset(newss)){ fechou = 1; break; }
                    if(op(tmp->formula))
                        insere(newAlpha, newBeta, newGama, newDelta, tmp->formula);
                }
            }

            for(tmp = delta->begin; tmp && !fechou; tmp = tmp->next){
                if(existsneg(newss, tmp->formula)) fechou = 1;
                else if(!exists(newss, tmp->formula)){
                    set(newss, tmp->formula->value_number);
                    if(issubset(newss)){
                        fechou = 1;
                        break;
                    }
                    /*#ifdef USESATCACHE
                      if(issubsetsat(newss)){
                      reset(&newss, tmp->->value_numberformula);
                      continue;
                      }
#endif*/

                    if(op(tmp->formula)){
                        insere(newAlpha, newBeta, newGama, newDelta, tmp->formula);
                        fechou = dfs(newAlpha, newBeta, newGama, newDelta, newss, ++neww);
                        tira(newAlpha, newBeta, newGama, newDelta, tmp->formula);
                    }
                    else fechou = dfs(newAlpha, newBeta, newGama, newDelta, newss, ++neww);

                    /*if(fechou) encache(&newss);
                      else{*/
                    // #ifdef USESATCACHE
                    //   if(!tmp->next && size < 5) encachesat(&newss);
                    //   else
                    // #endif
                    reset(newss, tmp->formula->value_number);
                    /*}*/
                }
                else fechou = dfs(newAlpha, newBeta, newGama, newDelta, newss, ++neww);
            }

            // #ifndef USESATCACHE
            newss = clean_set(newss);
            // #endif

            newAlpha = clean(newAlpha);
            newBeta = clean(newBeta);
            newGama = clean(newGama);
            newDelta = clean(newDelta);
        }
    }

    for(aux = cleandepois->begin; aux; aux = aux->next){
        if(aux->formula->type == DISJUNCTION ||
                aux->formula->type == BOX ||
                aux->formula->type == DIAMOND){
            tira(NULL, beta, gama, delta, aux->formula);
        }
        reset(ss, aux->formula->value_number);
    }

    cleandepois = clean(cleandepois);

    return fechou;
}

int formulasize;
int numsimp;
int verbose;

void recalc_hash(tnode *t){
    if(!t) return;
    if(t->left) recalc_hash(t->left);
    if(t->right) recalc_hash(t->right);

    if(t->list){
        formulalist *tmp;

        for(tmp = t->list; tmp; tmp = tmp->next)
            recalc_hash(tmp->formula);

        t->list->value_number = hash_list(t->list);
    }

    t->value_number = hash_tree(t);
}

int tempo;

void zera_vn(tnode *t){
    if(!t) return;
    t->value_number = 0;
    if(t->left) zera_vn(t->left);
    if(t->right) zera_vn(t->right);
    formulalist *tmp;
    for(tmp = t->list; tmp; tmp = tmp->next)
        zera_vn(tmp->formula);
}

void rename_vn(tnode *t){
    if(!t) return;
    if(t->value_number) return;
    t->value_number = tempo++;
    if(t->left) rename_vn(t->left);
    if(t->right) rename_vn(t->right);
    formulalist *tmp;
    for(tmp = t->list; tmp; tmp = tmp->next)
        rename_vn(tmp->formula);
}

void to_hash_set(tnode *t, hash **s){
    if(!t) return;
    add(s, t);
    if(t->left) to_hash_set(t->left, s);
    if(t->right) to_hash_set(t->right, s);
    formulalist *tmp;
    for(tmp = t->list; tmp; tmp = tmp->next)
        to_hash_set(tmp->formula, s);
}

void set_neg(tnode *t){
    if(!t) return;
    //printf("%d %d\n", t->value_number, cneg[ t->value_number ] );
    if(t->type == NEGATION){
        cneg[ t->left->value_number ] = t->value_number;
        cneg[ t->value_number ] = t->left->value_number;
    }
    if(t->left) set_neg(t->left);
    if(t->right) set_neg(t->right);
    formulalist *tmp;
    for(tmp = t->list; tmp; tmp = tmp->next)
        set_neg(tmp->formula);
}

tnode *dagfy(tnode *t){
    if(!t) return NULL;

    header *q = create_list();
    tnode *u;
    formulalist *tmp;
    hash *s = NULL;
    tnode *form;

    push_back(q, t);

    s = NULL;

    while(!empty(q)){
        u = front(q); pop_front(q);
        if(u->left){
            form = find(&s, u->left);

            if(form){
                u->left = free_tree(u->left);
                u->left = form;
                continue;
            }

            push_back(q, u->left);
            add(&s, u->left);
        }
        if(u->right){
          form = find(&s, u->right);

            if(form){
                u->right = free_tree(u->right);
                u->right = form;
                continue;
            }

            push_back(q, u->right);
            add(&s, u->right);
        }
        for(tmp = u->list; tmp; tmp = tmp->next){
            form = find(&s, tmp->formula);

            if(form){
                tmp->formula = free_tree(tmp->formula);
                tmp->formula = form;
                continue;
            }

            push_back(q, tmp->formula);
            add(&s, tmp->formula);
        }
    }

    zera_vn(t);
    rename_vn(t);
    clean_hash(&s);
    to_hash_set(t, &s);

    cneg = malloc(tempo*sizeof(int));
    memset(cneg, -1, tempo*sizeof(int));
    
    set_neg(t);

    clean_hash(&s);

    q = clean(q);

    return t;
}

int main(int argc, char* argv[]){
  int i;
  int fromfile = 0;

  for(i = 1; i < argc; i++){
    if(!strcmp(argv[i], "-f")){
      char *formula = malloc(snprintf(NULL, 0, "sos(formulas). %s. end_of_list.", argv[++i]) + 1);
      sprintf(formula, "sos(formulas). %s. end_of_list.", argv[i]);
      yy_scan_string(formula);
      free(formula);
    }
    else if(!strcmp(argv[i], "-i")){
      fromfile = 1;
      yyin = fopen(argv[++i], "r");
      if(!yyin){
        printf("\nInput file not found: %s\n", argv[i]);
        return 0;
      }
    }
    else if(!strcmp(argv[i], "-out")) OUT = 1;
  }

  symbol_table_init();
  
  yyparse();
  if(fromfile) fclose(yyin);
  yylex_destroy();
  clear_hashes();
  linearise = prenex = nnfsimp = ON;
  early_mlple = early_ple = ON;
  
  root = input_preprocessing(root);
  recalc_hash(root);
  root = dagfy(root);
  
  header *alpha = create_list();
  header *beta = create_list();
  header *gama = create_list();
  header *delta = create_list();

  {
      globalcache = malloc(sizeof(struct cache));
      globalcache->s = create_set(0);
      globalcache->next = globalcache;
  }
  {
      globalsatcache = malloc(sizeof(struct cache));
      globalsatcache->s = create_set(0);
      globalsatcache->next = globalsatcache;
  }

  int provou = 0;
  bitset *ss = create_set(tempo);
  if(is_false(root->left)) provou = 1;
  else if(op(root->left)){
    insere(alpha, beta, gama, delta, root->left);
    provou = dfs(alpha, beta, gama, delta, ss, ++neww);
    tira(alpha, beta, gama, delta, root->left);
  }

  printf("%s %lf %lf %d\n", provou ? "Unsatisfiable" : "Satisfiable", (double)(cost+costsat)/CLOCKS_PER_SEC, (double)costsat/CLOCKS_PER_SEC, globalcounter);
  if(OUT){

  }

  root = free_tree(root);

  alpha = clean(alpha);
  beta = clean(beta);
  gama = clean(gama);
  delta = clean(delta);

  {
    while(globalcache != globalcache->next){
      struct cache *tmp = globalcache->next; //onde tem que ser apagado
      globalcache->next = globalcache->next->next;
      tmp->s = clean_set(tmp->s);
      free(tmp);
    }
    globalcache->s = clean_set(globalcache->s);
    free(globalcache);
    globalcache = NULL;
  }

  {
    while(globalsatcache != globalsatcache->next){
      struct cache *tmp = globalsatcache->next; //onde tem que ser apagado
      globalsatcache->next = globalsatcache->next->next;
      tmp->s = clean_set(tmp->s);
      free(tmp);
    }
    globalsatcache->s = clean_set(globalsatcache->s);
    free(globalsatcache);
    globalsatcache = NULL;
  }

  clear_all();
  ss = clean_set(ss);
  return 0;
}
